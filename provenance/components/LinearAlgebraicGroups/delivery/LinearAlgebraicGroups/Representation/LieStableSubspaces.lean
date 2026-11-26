import Specs.LinearAlgebraicGroups.Representation.LieStableSubspaces
import LinearAlgebraicGroups.Affine.CharacteristicZeroSmoothness
import LinearAlgebraicGroups.Affine.ClosedSubgroups
import LinearAlgebraicGroups.Affine.IdentityTangent
import LinearAlgebraicGroups.Affine.RationalRepresentations
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.RingTheory.Ideal.IdempotentFG
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite WithConv
open Coalgebra Bialgebra HopfAlgebra TensorProduct
open scoped TensorProduct CategoryTheory.MonObj CategoryTheory.GrpObj

universe u

namespace LinearAlgebraicGroups

noncomputable section

set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

open RationalRepresentations
open Specs.AdvCommAlg.Differentials.Tangent

variable {k : Type u} [Field k]

private theorem factorsThroughQuotient {A R : Type u} [CommRing A] [Algebra k A]
    [CommRing R] [Algebra k R] (I : Ideal A) (g : A →ₐ[k] R) :
    (∃ h : (A ⧸ I) →ₐ[k] R, h.comp (Ideal.Quotient.mkₐ k I) = g) ↔
      I ≤ RingHom.ker g.toRingHom := by
  constructor
  · rintro ⟨h, rfl⟩ x hx
    change h (Ideal.Quotient.mk I x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  · intro h
    exact ⟨Ideal.Quotient.liftₐ I g h, rfl⟩

private theorem quotientConvolution {A : HopfAlgebraCategory k} (I : Ideal A)
    [I.IsHopfIdeal k] (R : TestAlgebra k)
    (f g : (convolutionPoints (hopfQuotient A I)).obj R) :
    let q := (hopfQuotientMap A I).hom.toAlgHom
    (toConv (f.ofConv.comp q) * toConv (g.ofConv.comp q)).ofConv = (f * g).ofConv.comp q := by
  intro q
  apply AlgHom.ext
  intro x
  rw [AlgHom.comp_apply]
  change (toConv (f.ofConv.comp q) * toConv (g.ofConv.comp q)) x =
    ((f * g).ofConv) (q x)
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply]
  have hq := CoalgHomClass.map_comp_comul_apply (hopfQuotientMap A I).hom x
  change Algebra.TensorProduct.map q q (comul (R := k) x) = comul (R := k) (q x) at hq
  rw [← hq]
  have ht : Algebra.TensorProduct.lift (f.ofConv.comp q) (g.ofConv.comp q)
        (fun _ _ ↦ Commute.all _ _) =
      (Algebra.TensorProduct.lift f.ofConv g.ofConv (fun _ _ ↦ Commute.all _ _)).comp
        (Algebra.TensorProduct.map q q) := by
    apply Algebra.TensorProduct.ext
    · ext y
      simp
    · ext y
      simp
  exact DFunLike.congr_fun ht _

private theorem full_tangent_le_augmentation_sq {A : HopfAlgebraCategory k}
    (I : Ideal A) [I.IsHopfIdeal k]
    (h : ∀ x : HopfTangentPoint A, I ≤ RingHom.ker x.val.toRingHom) :
    I ≤ (IdentityTangent.augmentationIdeal A) ^ 2 := by
  let e := counitAlgHom k A
  obtain ⟨φ, hφ, _⟩ := pointTangentLifts k A e
  intro a ha
  have he : a ∈ IdentityTangent.augmentationIdeal A :=
    Submodule.IsCoideal.counit_eq_zero (I := I.restrictScalars k) ha
  let b : IdentityTangent.augmentationIdeal A := ⟨a, he⟩
  have hb : (IdentityTangent.augmentationIdeal A).toCotangent b = 0 := by
    apply (Module.forall_dual_apply_eq_zero_iff k _).mp
    intro l
    rw [← hφ l b]
    have hz : (φ l).val a = 0 := h (φ l) ha
    simp [b, hz]
  exact (Ideal.toCotangent_eq_zero _ b).mp hb

/-- The first-order thickening of a smooth closed subgroup splits. After
translation by that section, its universal point reduces to the identity.
When the augmentation square contains the ideal, this forces the ideal
to coincide with its square. -/
private theorem hopfIdeal_sq_eq {A : HopfAlgebraCategory k} (I : Ideal A)
    [I.IsHopfIdeal k] [Algebra.FormallySmooth k (A ⧸ I)]
    (hI : I ≤ (IdentityTangent.augmentationIdeal A) ^ 2) :
    I ^ 2 = I := by
  let R := CommAlgCat.of k (A ⧸ I ^ 2)
  let B := hopfQuotient A I
  let q : A →ₐ[k] B := Ideal.Quotient.mkₐ k I
  let f : A →ₐ[k] R := Ideal.Quotient.mkₐ k (I ^ 2)
  have hle : I ^ 2 ≤ I := by
    rw [pow_two]
    exact Ideal.mul_le_left
  let r : R →ₐ[k] B := Ideal.Quotient.factorₐ k hle
  have hr : r.comp f = q := rfl
  have hrs : Function.Surjective r := by
    intro b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨f a, rfl⟩
  have hrk : RingHom.ker r.toRingHom = I.map f.toRingHom := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change r (f a) = 0 ↔ f a ∈ I.map f.toRingHom
    rw [show r (f a) = q a from rfl]
    change q a = 0 ↔ a ∈ Ideal.comap (Ideal.Quotient.mk (I ^ 2))
      (I.map (Ideal.Quotient.mk (I ^ 2)))
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    change q a = 0 ↔ a ∈ I ⊔ RingHom.ker (Ideal.Quotient.mk (I ^ 2))
    rw [Ideal.mk_ker, sup_eq_left.mpr hle]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hsq : RingHom.ker r.toRingHom ^ 2 = ⊥ := by
    rw [hrk, ← Ideal.map_pow]
    change (I ^ 2).map (Ideal.Quotient.mk (I ^ 2)) = ⊥
    exact (congrArg (Ideal.map (Ideal.Quotient.mk (I ^ 2)))
      (Ideal.mk_ker (I := I ^ 2))).symm.trans (RingHom.map_ker _)
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k B) r hrs ⟨2, hsq⟩
  have hs : r.comp s = AlgHom.id k B := by
    ext x
    change r (s x) = x
    exact Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id k B) r hrs _ x
  let F := convolutionPoints A
  let red := (F.map (CommAlgCat.ofHom r)).hom
  let a : F.obj R := toConv f
  let b : F.obj R := toConv (s.comp q)
  let c : F.obj R := a * b⁻¹
  have hab : red a = red b := by
    apply WithConv.ofConv_injective
    change r.comp f = r.comp (s.comp q)
    rw [← AlgHom.comp_assoc, hs, AlgHom.id_comp, hr]
  have hc : red c = 1 := by rw [show c = a * b⁻¹ from rfl, map_mul, map_inv, hab, mul_inv_cancel]
  have hm : IdentityTangent.augmentationIdeal A ≤
      Ideal.comap c.ofConv.toRingHom (RingHom.ker r.toRingHom) := by
    intro x hx
    change r (c.ofConv x) = 0
    change (red c).ofConv x = 0
    rw [hc]
    change (1 : WithConv (A →ₐ[k] B)) x = 0
    rw [AlgHom.convOne_apply, show counit (R := k) x = 0 from hx, map_zero]
  have hcz : I ≤ RingHom.ker c.ofConv.toRingHom := by
    refine hI.trans ?_
    change (IdentityTangent.augmentationIdeal A) ^ 2 ≤
      Ideal.comap c.ofConv.toRingHom ⊥
    apply (Ideal.map_le_iff_le_comap).mp
    rw [Ideal.map_pow]
    exact (pow_le_pow_left' (Ideal.map_le_iff_le_comap.mpr hm) 2).trans_eq hsq
  obtain ⟨t, ht⟩ := (factorsThroughQuotient I c.ofConv).mpr hcz
  have he : a = c * b := by simp [a, b, c]
  have hf : f = (toConv t * toConv s : (convolutionPoints B).obj R).ofConv.comp q := by
    have he' := congrArg WithConv.ofConv he
    change f = (toConv c.ofConv * toConv (s.comp q)).ofConv at he'
    rw [← ht] at he'
    exact he'.trans (quotientConvolution I R (toConv t) (toConv s))
  refine le_antisymm hle ?_
  intro x hx
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change f x = 0
  rw [hf, AlgHom.comp_apply, show q x = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

private theorem hopfIdeal_eq_bot_of_full_tangent [CharZero k]
    (A : HopfAlgebraCategory k) [Algebra.FiniteType k A] [ConnectedSpace (PrimeSpectrum A)]
    (I : Ideal A) [I.IsHopfIdeal k]
    (h : ∀ x : HopfTangentPoint A, I ≤ RingHom.ker x.val.toRingHom) : I = ⊥ := by
  let B := hopfQuotient A I
  have : Algebra.FiniteType k B :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k I) Ideal.Quotient.mk_surjective
  let G : Specs.AffineAlgebraicGroup k :=
    ⟨specGroup B, ((affineHopfSpec k).obj (op B)).property,
      (hopfSpec_locallyOfFiniteType_iff k B).mpr inferInstance, by
        change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k B)))
        infer_instance⟩
  have hs := characteristicZeroSmoothness k G
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) at hs
  have : Algebra.Smooth k B :=
    RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hs)
  have eI : IsIdempotentElem I := by
    change I * I = I
    exact (pow_two I).symm.trans (hopfIdeal_sq_eq I (full_tangent_le_augmentation_sq I h))
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨e, he, hIe⟩ := (Ideal.isIdempotentElem_iff_of_fg I (IsNoetherian.noetherian I)).mp eI
  have heI : e ∈ I := by rw [hIe]; exact Submodule.mem_span_singleton_self _
  have hε : counit (R := k) e = 0 :=
    Submodule.IsCoideal.counit_eq_zero (I := I.restrictScalars k) heI
  have hcl : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum A)) :=
    (PrimeSpectrum.isClopen_iff).mpr ⟨e, he, rfl⟩
  have hnot : (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum A)) ≠ Set.univ := by
    intro hu
    let z : PrimeSpectrum A := ⟨RingHom.ker (counitAlgHom k A).toRingHom,
      RingHom.ker_isPrime _⟩
    have hz : z ∈ (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum A)) := hu ▸ Set.mem_univ _
    exact hz hε
  have hempty : (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum A)) = ∅ :=
    (isClopen_iff.mp hcl).resolve_right hnot
  have he0 : e = 0 := by
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he .zero
    rw [PrimeSpectrum.basicOpen_zero]
    exact SetLike.coe_injective hempty
  rw [hIe, he0, Submodule.span_zero_singleton]


private abbrev BlockIndex (p q : ℕ) := ULift.{u} (Fin p ⊕ Fin q)

section MatrixStabilizer

variable {p q : ℕ}

private def PreservesFirstBlock {R : Type u} [CommRing R]
    (M : Matrix (BlockIndex.{u} p q) (BlockIndex.{u} p q) R) : Prop :=
  ∀ (i : Fin p) (j : Fin q), M (.up (.inr j)) (.up (.inl i)) = 0

private theorem preservesFirstBlock_one {R : Type u} [CommRing R] :
    PreservesFirstBlock (1 : Matrix (BlockIndex.{u} p q) (BlockIndex.{u} p q) R) := by
  intro i j
  simp

private theorem PreservesFirstBlock.mul {R : Type u} [CommRing R]
    {M N : Matrix (BlockIndex.{u} p q) (BlockIndex.{u} p q) R}
    (hM : PreservesFirstBlock M) (hN : PreservesFirstBlock N) :
    PreservesFirstBlock (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro l _
  rcases l with ⟨l | l⟩
  · rw [hM l j, zero_mul]
  · rw [hN i l, mul_zero]

variable (A : HopfAlgebraCategory k)
  (M : Matrix (BlockIndex.{u} p q) (BlockIndex.{u} p q) A)

private def blockStabilizerIdeal : Ideal A :=
  Ideal.span {x | (∃ (i : Fin p) (j : Fin q), x = M (.up (.inr j)) (.up (.inl i))) ∨
    (∃ (i : Fin p) (j : Fin q), x = antipode k (M (.up (.inr j)) (.up (.inl i))))}

variable (hM : IsCoactionMatrix A M)

private theorem blockStabilizerIdeal_iff (R : TestAlgebra k)
    (g : (convolutionPoints A).obj R) :
    blockStabilizerIdeal A M ≤ RingHom.ker g.ofConv.toRingHom ↔
      PreservesFirstBlock ((matrixPointHom A M hM).app R g).val ∧
      PreservesFirstBlock ((matrixPointHom A M hM).app R g⁻¹).val := by
  rw [blockStabilizerIdeal, Ideal.span_le]
  constructor
  · intro h
    exact ⟨fun i j ↦ h (Or.inl ⟨i, j, rfl⟩), fun i j ↦ h (Or.inr ⟨i, j, rfl⟩)⟩
  · rintro ⟨h, hi⟩ x (⟨i, j, rfl⟩ | ⟨i, j, rfl⟩)
    · exact h i j
    · exact hi i j

include hM in
private theorem blockStabilizerIdeal_isHopf : (blockStabilizerIdeal A M).IsHopfIdeal k := by
  let I := blockStabilizerIdeal A M
  let B := A ⧸ I
  let q : A →ₐ[k] B := Ideal.Quotient.mkₐ k I
  have hq : I ≤ RingHom.ker q.toRingHom := by
    intro a ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  let hblock (R : TestAlgebra k) (g : (convolutionPoints A).obj R) :=
    blockStabilizerIdeal_iff A M hM R g
  refine { toIsCoideal := ⟨?_, ?_⟩, antipode_mem := ?_ }
  · intro x hx
    let R := CommAlgCat.of k k
    have h := (hblock R 1).mpr (by simp only [inv_one, map_one]; exact
      ⟨preservesFirstBlock_one, preservesFirstBlock_one⟩)
    exact h hx
  · intro x hx
    let R := CommAlgCat.of k (B ⊗[k] B)
    let l : (convolutionPoints A).obj R :=
      toConv ((Algebra.TensorProduct.includeLeft : B →ₐ[k] R).comp q)
    let r : (convolutionPoints A).obj R :=
      toConv ((Algebra.TensorProduct.includeRight : B →ₐ[k] R).comp q)
    have hl := (hblock R l).mp (by
      intro a ha
      change (Algebra.TensorProduct.includeLeft : B →ₐ[k] R) (q a) = 0
      rw [show q a = 0 from hq ha, map_zero])
    have hr := (hblock R r).mp (by
      intro a ha
      change (Algebra.TensorProduct.includeRight : B →ₐ[k] R) (q a) = 0
      rw [show q a = 0 from hq ha, map_zero])
    let α := ((matrixPointHom A M hM).app R).hom
    have hm : I ≤ RingHom.ker (l * r).ofConv.toRingHom :=
      (hblock R (l * r)).mpr (by
        change PreservesFirstBlock (α (l * r)).val ∧
          PreservesFirstBlock (α ((l * r)⁻¹)).val
        rw [mul_inv_rev, map_mul, map_mul, Units.val_mul, Units.val_mul]
        exact ⟨hl.1.mul hr.1, hr.2.mul hl.2⟩)
    have hh : (l * r).ofConv x = 0 := hm hx
    change TensorProduct.map q.toLinearMap q.toLinearMap (comul (R := k) x) = 0
    change (toConv l.ofConv * toConv r.ofConv) x = 0 at hh
    rw [AlgHom.convMul_apply] at hh
    have hmap : Algebra.TensorProduct.lift l.ofConv r.ofConv (fun _ _ ↦ Commute.all _ _) =
        Algebra.TensorProduct.map q q := by
      apply Algebra.TensorProduct.ext
      · rw [Algebra.TensorProduct.lift_comp_includeLeft]
        apply AlgHom.ext
        intro a
        change (Algebra.TensorProduct.includeLeft.comp q : A →ₐ[k] R) a =
          ((Algebra.TensorProduct.map q q).comp Algebra.TensorProduct.includeLeft) a
        simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
          Algebra.TensorProduct.map_tmul, map_one]
      · rw [Algebra.TensorProduct.lift_comp_includeRight]
        apply AlgHom.ext
        intro a
        change (Algebra.TensorProduct.includeRight.comp q : A →ₐ[k] R) a =
          ((Algebra.TensorProduct.map q q).comp Algebra.TensorProduct.includeRight) a
        simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.map_tmul, map_one]
    rw [hmap] at hh
    exact hh
  · intro x hx
    let R := CommAlgCat.of k B
    let g : (convolutionPoints A).obj R := toConv q
    have h := (hblock R g).mp hq
    have hi := (hblock R g⁻¹).mpr ⟨h.2, by simpa only [inv_inv] using h.1⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hi hx)

end MatrixStabilizer

open private tensorCoordinate_tmul tensorCoordinate_sum_basis tensor_eq_sum_basis
  from LinearAlgebraicGroups.Affine.RationalRepresentations

section Coordinates

variable {V : Type u} [AddCommGroup V] [Module k V]
  {p q : ℕ} (b : Module.Basis (BlockIndex.{u} p q) k V) (W : Submodule k V)

private theorem exists_adapted_basis [FiniteDimensional k V] (W : Submodule k V) :
    ∃ (p q : ℕ) (b : Module.Basis (BlockIndex.{u} p q) k V),
      Submodule.span k (Set.range (fun i : Fin p ↦ b (.up (.inl i)))) = W := by
  obtain ⟨U, hU⟩ := W.exists_isCompl
  let bW := Module.finBasis k W
  let bU := Module.finBasis k U
  let b := ((bW.prod bU).map (W.prodEquivOfIsCompl U hU)).reindex Equiv.ulift.symm
  refine ⟨_, _, b, ?_⟩
  have hb (i : Fin (Module.finrank k W)) : b (.up (.inl i)) = (bW i : V) := by
    simp [b]
  simp_rw [hb]
  change Submodule.span k (Set.range (W.subtype ∘ bW)) = W
  rw [Set.range_comp W.subtype bW, ← Submodule.map_span, bW.span_eq, Submodule.map_subtype_top]

private theorem tensor_mem_iff {R : Type u} [CommRing R] [Algebra k R]
    (hspan : Submodule.span k (Set.range (fun i : Fin p ↦ b (.up (.inl i)))) = W)
    (z : V ⊗[k] R) :
    z ∈ LinearMap.range (W.subtype.rTensor R) ↔
      ∀ j : Fin q, tensorCoordinate b (.up (.inr j)) z = 0 := by
  classical
  constructor
  · rintro ⟨t, rfl⟩ j
    let i : BlockIndex.{u} p q := .up (.inr j)
    have hc : W ≤ LinearMap.ker (b.coord i) := by
      rw [← hspan]
      apply Submodule.span_le.mpr
      rintro _ ⟨l, rfl⟩
      simp [i, LinearMap.mem_ker, Module.Basis.coord_apply]
    have hzero : (tensorCoordinate b i).comp (W.subtype.rTensor R) = 0 := by
      apply TensorProduct.ext'
      intro w r
      change tensorCoordinate b i ((w : V) ⊗ₜ[k] r) = 0
      rw [tensorCoordinate_tmul, LinearMap.mem_ker.mp (hc w.2), zero_smul]
    exact LinearMap.congr_fun hzero t
  · intro h
    rw [← tensor_eq_sum_basis b z]
    apply Submodule.sum_mem
    intro i _
    rcases i with ⟨i | j⟩
    · have hi : b (.up (.inl i)) ∈ W := hspan ▸ Submodule.subset_span ⟨i, rfl⟩
      exact ⟨(⟨_, hi⟩ : W) ⊗ₜ[k] tensorCoordinate b (.up (.inl i)) z, rfl⟩
    · simp only [h j, TensorProduct.tmul_zero, zero_mem]

private theorem point_preserves_iff (A : HopfAlgebraCategory k) (ρ : RightComodule k A V)
    (hspan : Submodule.span k (Set.range (fun i : Fin p ↦ b (.up (.inl i)))) = W)
    (R : TestAlgebra k) (g : (convolutionPoints A).obj R) :
    (∀ v : W, evaluate A ρ g.ofConv v ∈ LinearMap.range (W.subtype.rTensor R)) ↔
      PreservesFirstBlock
        ((matrixPointHom A _ (coefficients_isCoactionMatrix A b ρ)).app R g).val := by
  let L := evaluate A ρ g.ofConv
  have hb (i : Fin p) (j : Fin q) :
      tensorCoordinate b (.up (.inr j)) (L (b (.up (.inl i)))) =
        g.ofConv (coefficients A b ρ (.up (.inr j)) (.up (.inl i))) := by
    have hsum : L (b (.up (.inl i))) =
        ∑ a, b a ⊗ₜ[k] g.ofConv (coefficients A b ρ a (.up (.inl i))) := by
      change (g.ofConv.toLinearMap.lTensor V) (ρ.coaction (b (.up (.inl i)))) = _
      rw [coaction_apply_basis A b ρ]
      simp
    rw [hsum, tensorCoordinate_sum_basis]
  change (∀ v : W, L v ∈ _) ↔ _
  simp_rw [tensor_mem_iff b W hspan (L _)]
  constructor
  · intro h i j
    have hw : b (.up (.inl i)) ∈ W := hspan ▸ Submodule.subset_span ⟨i, rfl⟩
    exact (hb i j).symm.trans (h ⟨_, hw⟩ j)
  · intro h v j
    let f := (tensorCoordinate b (.up (.inr j))).comp L
    have hle : W ≤ LinearMap.ker f := by
      rw [← hspan]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact (hb i j).trans (h i j)
    exact hle v.2

end Coordinates


section Tangent

variable {V : Type u} [AddCommGroup V] [Module k V]

private abbrev dualFstTensor (V : Type u) [AddCommGroup V] [Module k V] :
    V ⊗[k] DualNumber k →ₗ[k] V :=
  (TensorProduct.rid k V).toLinearMap.comp ((TrivSqZeroExt.fstHom k k k).toLinearMap.lTensor V)

private abbrev dualSndTensor (V : Type u) [AddCommGroup V] [Module k V] :
    V ⊗[k] DualNumber k →ₗ[k] V :=
  (TensorProduct.rid k V).toLinearMap.comp ((TrivSqZeroExt.sndHom k k).lTensor V)

private abbrev epsilon : DualNumber k := TrivSqZeroExt.inr 1

private theorem dual_tensor_split (z : V ⊗[k] DualNumber k) :
    z = dualFstTensor V z ⊗ₜ[k] (1 : DualNumber k) + dualSndTensor V z ⊗ₜ[k] epsilon := by
  induction z using TensorProduct.inductionOn with
  | tmul v a =>
    change v ⊗ₜ[k] a = (a.fst • v) ⊗ₜ[k] _ + (a.snd • v) ⊗ₜ[k] _
    rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul, ← TensorProduct.tmul_add]
    congr 1
    apply TrivSqZeroExt.ext <;>
      simp [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_smul,
        TrivSqZeroExt.snd_smul]
  | add a b ha hb =>
    rw [map_add, map_add, TensorProduct.add_tmul, TensorProduct.add_tmul, add_add_add_comm]
    exact congrArg₂ (· + ·) ha hb

private theorem tangent_evaluation (A : HopfAlgebraCategory k) (ρ : RightComodule k A V)
    (x : HopfTangentPoint A) (v : V) :
    evaluate A ρ x.val v = v ⊗ₜ[k] (1 : DualNumber k) +
      differentiatedCoaction A ρ x v ⊗ₜ[k] epsilon := by
  have h : dualFstTensor V (evaluate A ρ x.val v) = v := by
    change TensorProduct.rid k V (((TrivSqZeroExt.fstHom k k k).toLinearMap.lTensor V)
      ((x.val.toLinearMap.lTensor V) (ρ.coaction v))) = v
    rw [← LinearMap.lTensor_comp_apply,
      show (TrivSqZeroExt.fstHom k k k).toLinearMap.comp x.val.toLinearMap =
        Coalgebra.counit (R := k) (A := A) from
        congrArg AlgHom.toLinearMap x.property]
    exact ρ.counit v
  change _ = v ⊗ₜ[k] (1 : DualNumber k) + dualSndTensor V (evaluate A ρ x.val v) ⊗ₜ[k] epsilon
  simpa only [h] using dual_tensor_split (evaluate A ρ x.val v)

private theorem tangent_evaluate_mem_iff (A : HopfAlgebraCategory k)
    (ρ : RightComodule k A V) (W : Submodule k V) (x : HopfTangentPoint A) (v : W) :
    evaluate A ρ x.val v ∈ LinearMap.range (W.subtype.rTensor (DualNumber k)) ↔
      differentiatedCoaction A ρ x v ∈ W := by
  constructor
  · rintro ⟨t, ht⟩
    have hl : (dualSndTensor V).comp (W.subtype.rTensor (DualNumber k)) =
        W.subtype.comp (dualSndTensor W) := by
      apply TensorProduct.ext'
      intro w a
      simp [dualSndTensor]
    have hs := LinearMap.congr_fun hl t
    change dualSndTensor V ((W.subtype.rTensor (DualNumber k)) t) = _ at hs
    rw [ht] at hs
    change differentiatedCoaction A ρ x v = _ at hs
    rw [hs]
    exact (dualSndTensor W t).2
  · intro h
    let w : W := ⟨differentiatedCoaction A ρ x v, h⟩
    refine ⟨v ⊗ₜ[k] (1 : DualNumber k) + w ⊗ₜ[k] epsilon, ?_⟩
    simp only [map_add, LinearMap.rTensor_tmul, Submodule.subtype_apply]
    exact (tangent_evaluation A ρ x v).symm

private abbrev dualTest (k : Type u) [Field k] : TestAlgebra k :=
  CommAlgCat.of k (DualNumber k)

private def inverseTangent {A : HopfAlgebraCategory k} (x : HopfTangentPoint A) :
    HopfTangentPoint A := by
  let F := convolutionPoints A
  let g : F.obj (dualTest k) := toConv x.val
  let r := (F.map (dualReduction k)).hom
  have hg : r g = 1 := congrArg toConv x.property
  refine ⟨(g⁻¹).ofConv, ?_⟩
  apply WithConv.toConv_injective
  change r (g⁻¹) = 1
  rw [map_inv, hg, inv_one]

open private snd_conv from LinearAlgebraicGroups.Affine.IdentityTangent in
private theorem inverse_differential (A : HopfAlgebraCategory k) (ρ : RightComodule k A V)
    (x : HopfTangentPoint A) :
    differentiatedCoaction A ρ (inverseTangent x) = - differentiatedCoaction A ρ x := by
  let S := TrivSqZeroExt.sndHom k k
  have hs : S.comp (inverseTangent x).val.toLinearMap = -(S.comp x.val.toLinearMap) := by
    ext a
    change ((inverseTangent x).val a).snd = -(x.val a).snd
    have hz := snd_conv (inverseTangent x) x a
    let g : (convolutionPoints A).obj (dualTest k) := toConv x.val
    have hg : (toConv (inverseTangent x).val * toConv x.val :
        WithConv (A →ₐ[k] DualNumber k)) = 1 :=
      (inv_mul_cancel g : g⁻¹ * g = 1)
    rw [hg] at hz
    change ((TrivSqZeroExt.inlAlgHom k k k) (counit (R := k) a)).snd =
      ((inverseTangent x).val a).snd + (x.val a).snd at hz
    exact eq_neg_of_add_eq_zero_left hz.symm
  ext v
  change TensorProduct.rid k V ((S.lTensor V) (((inverseTangent x).val.toLinearMap.lTensor V)
      (ρ.coaction v))) =
    -TensorProduct.rid k V ((S.lTensor V) ((x.val.toLinearMap.lTensor V) (ρ.coaction v)))
  rw [← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply, hs]
  simp

private theorem tangent_preserves_iff (A : HopfAlgebraCategory k)
    (ρ : RightComodule k A V) (W : Submodule k V) (x : HopfTangentPoint A) :
    PreservesSubspace A ρ W (dualTest k) (toConv x.val) ↔
      ∀ v : W, differentiatedCoaction A ρ x v ∈ W := by
  constructor
  · intro h v
    exact (tangent_evaluate_mem_iff A ρ W x v).mp (h.1 v)
  · intro h
    refine ⟨fun v ↦ (tangent_evaluate_mem_iff A ρ W x v).mpr (h v), fun v ↦ ?_⟩
    apply (tangent_evaluate_mem_iff A ρ W (inverseTangent x) v).mpr
    rw [inverse_differential, LinearMap.neg_apply]
    exact W.neg_mem (h v)

end Tangent


open private dualKernelIso from LinearAlgebraicGroups.Affine.IdentityTangent

private def lieTangentEquiv (A : HopfAlgebraCategory k) :
    Specs.Lie k (specGroup A) ≃ HopfTangentPoint A :=
  (dualKernelIso (hopfSpecPointIso A)).symm.toEquiv.trans (hopfKernelLifts A)

private theorem lieTangentEquiv_apply (A : HopfAlgebraCategory k)
    (x : Specs.Lie k (specGroup A)) :
    lieTangentEquiv A x = tangentPointOfLie A x := rfl

private theorem tangentPoint_natural {A B : HopfAlgebraCategory k} (q : A ⟶ B)
    (x : Specs.Lie k (specGroup B)) :
    (tangentPointOfLie A (mapPointKernel (specGroupMap q) x)).val =
      (tangentPointOfLie B x).val.comp q.hom.toAlgHom := by
  let R := dualTest k
  let ea := Spec.mapMulEquiv (R := k) (S := A) (T := R)
  let eb := Spec.mapMulEquiv (R := k) (S := B) (T := R)
  let y := (x.toMul.val : Points (specGroup B).X R)
  change (ea.symm (y ≫ (specGroupMap q).hom.hom)).ofConv = (eb.symm y).ofConv.comp q.hom.toAlgHom
  apply WithConv.toConv_injective
  change ea.symm (y ≫ (specGroupMap q).hom.hom) =
    toConv ((eb.symm y).ofConv.comp q.hom.toAlgHom)
  apply ea.injective
  rw [ea.apply_symm_apply]
  apply Over.OverMorphism.ext
  change y.left ≫ (specGroupMap q).hom.hom.left =
    Spec.map (CommRingCat.ofHom (((eb.symm y).ofConv.comp q.hom.toAlgHom).toRingHom))
  rw [(hopfSpecMorphism k q).1, show y.left = Spec.map
    (CommRingCat.ofHom (eb.symm y).ofConv.toRingHom) from
      congrArg (fun z : Points (specGroup B).X R ↦ z.left) (eb.apply_symm_apply y).symm]
  exact (Spec.map_comp (CommRingCat.ofHom q.hom.toAlgHom.toRingHom)
    (CommRingCat.ofHom (eb.symm y).ofConv.toRingHom)).symm

private theorem tangent_factors_iff {A : HopfAlgebraCategory k} (I : Ideal A)
    [I.IsHopfIdeal k] (x : HopfTangentPoint A) :
    (∃ y : HopfTangentPoint (hopfQuotient A I),
      y.val.comp (hopfQuotientMap A I).hom.toAlgHom = x.val) ↔
      I ≤ RingHom.ker x.val.toRingHom := by
  rw [← factorsThroughQuotient I x.val]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y.val, hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨⟨y, ?_⟩, hy⟩
    ext b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) b
    have h := DFunLike.congr_fun hy a
    change y (Ideal.Quotient.mk I a) = x.val a at h
    change (y (Ideal.Quotient.mk I a)).fst = _
    rw [h, show (x.val a).fst = counit (R := k) a from DFunLike.congr_fun x.property a]
    exact (CoalgHomClass.counit_comp_apply (hopfQuotientMap A I).hom a).symm

theorem lieSubspaceStabilizer : Specs.LieSubspaceStabilizer.{u} := by
  classical
  intro k V _ _ _ _ A ρ W
  obtain ⟨p, q, b, hspan⟩ := exists_adapted_basis W
  let M := coefficients A b ρ
  let hM := coefficients_isCoactionMatrix A b ρ
  let I := blockStabilizerIdeal A M
  let hI : I.IsHopfIdeal k := blockStabilizerIdeal_isHopf A M hM
  let i := specGroupMap (hopfQuotientMap A I)
  have hs (R : TestAlgebra k) (g : (convolutionPoints A).obj R) :
      PreservesSubspace A ρ W R g ↔ I ≤ RingHom.ker g.ofConv.toRingHom := by
    rw [blockStabilizerIdeal_iff A M hM]
    unfold PreservesSubspace
    exact and_congr (point_preserves_iff b W A ρ hspan R g)
      (point_preserves_iff b W A ρ hspan R g⁻¹)
  refine ⟨I, hI, (hopfMapClosedImmersion k _).mpr Ideal.Quotient.mk_surjective,
    fun R g ↦ (hs R g).trans (factorsThroughQuotient I g.ofConv).symm, ?_, ?_⟩
  · intro x y h
    apply (lieTangentEquiv (hopfQuotient A I)).injective
    rw [lieTangentEquiv_apply, lieTangentEquiv_apply]
    apply Subtype.ext
    apply AlgHom.ext
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) a
    have he := congrArg (fun z ↦ (tangentPointOfLie A z).val) h
    rw [tangentPoint_natural, tangentPoint_natural] at he
    exact DFunLike.congr_fun he a
  · ext x
    change (∃ y, mapPointKernel i y = x) ↔
      ∀ v : W, differentiatedCoaction A ρ (tangentPointOfLie A x) v ∈ W
    rw [← tangent_preserves_iff, hs, ← tangent_factors_iff I]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨tangentPointOfLie (hopfQuotient A I) y, (tangentPoint_natural _ _).symm⟩
    · rintro ⟨y, hy⟩
      obtain ⟨z, hz⟩ := (lieTangentEquiv (hopfQuotient A I)).surjective y
      rw [lieTangentEquiv_apply] at hz
      refine ⟨z, (lieTangentEquiv A).injective ?_⟩
      rw [lieTangentEquiv_apply, lieTangentEquiv_apply]
      apply Subtype.ext
      rwa [tangentPoint_natural, hz]

theorem lieStableSubspaces : Specs.LieStableSubspaces.{u} := by
  intro k V _ _ _ _ _ A _ _ ρ W
  constructor
  · intro h x
    let g : (convolutionPoints A).obj (dualTest k) := toConv (tangentPointOfLie A x).val
    have hv := (stableSubspaces A ρ W).mpr h
    exact (tangent_preserves_iff A ρ W (tangentPointOfLie A x)).mp
      ⟨hv _ g.ofConv, hv _ (g⁻¹).ofConv⟩
  · intro h
    obtain ⟨I, hI, _, hstab, _, _⟩ := lieSubspaceStabilizer A ρ W
    have hall (x : HopfTangentPoint A) : I ≤ RingHom.ker x.val.toRingHom := by
      obtain ⟨y, hy⟩ := (lieTangentEquiv A).surjective x
      rw [lieTangentEquiv_apply] at hy
      apply (factorsThroughQuotient I x.val).mp
      apply (hstab (dualTest k) (toConv x.val)).mp
      exact (tangent_preserves_iff A ρ W x).mpr (hy ▸ h y)
    have hbot := hopfIdeal_eq_bot_of_full_tangent A I hall
    apply (stableSubspaces A ρ W).mp
    intro R g
    have hf := (factorsThroughQuotient I g).mpr (by simp [hbot])
    exact ((hstab R (toConv g)).mpr hf).1

theorem lieStableSubspacesOfPresentation : Specs.LieStableSubspacesOfPresentation.{u} := by
  intro k V _ _ _ _ _ G hconn A e ρ W
  let f := ((Grp.forget (SchemeOver k)) ⋙ Over.forget _).mapIso e
  let : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  have hft : LocallyOfFiniteType (f.hom ≫ G.val.X.hom) := inferInstance
  have hf : f.hom ≫ G.val.X.hom = (specGroup A).X.hom := Over.w e.hom.hom.hom
  rw [hf] at hft
  let : Algebra.FiniteType k A := (hopfSpec_locallyOfFiniteType_iff k A).mp hft
  let : ConnectedSpace (PrimeSpectrum A) :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso f)).connectedSpace_iff.mpr hconn
  let d := dualKernelIso ((groupPointsFunctor k).mapIso e)
  rw [lieStableSubspaces A ρ W]
  constructor
  · intro h x
    exact h (mapPointKernel e.inv x)
  · intro h x
    have hx := h (d x)
    change ∀ v : W, differentiatedCoaction A ρ (tangentPointOfLie A (d.symm (d x))) v ∈ W at hx
    rwa [AddEquiv.symm_apply_apply] at hx

theorem lieStableGraphs : Specs.LieStableGraphs.{u} := by
  intro k V U _ _ _ _ _ _ _ _ A _ _ ρ f
  exact lieStableSubspaces A ρ f.graph

end
end LinearAlgebraicGroups
