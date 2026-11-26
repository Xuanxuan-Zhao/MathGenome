import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.ExactOperations
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.Criteria
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Coalgebra Opposite WithConv
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Unipotent

noncomputable section

open Specs (AffineAlgebraicGroup GroupScheme)
open Specs.Unipotent
open RationalRepresentations

open private invariant_iff_coaction tmul_mem_tensorFiltration
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.Criteria
open private groupPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private extendedGroupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private exists_relativeShear from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.HopfFaithfulFlatness
open private kernelQuotientMap_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.NilpotentAugmentationFlatness

variable {k : Type u} [Field k]

private lemma unipotent_iff_exists_embedding (G : AffineAlgebraicGroup k) :
    IsUnipotent G ↔ EmbedsUnitriangular G := by
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation G
  obtain ⟨h₁, h₂, h₃, _⟩ := unipotenceCriteria G A e
  exact h₁.trans (h₂.trans h₃)

theorem closedSubgroupsUnipotent : ClosedSubgroupsUnipotent.{u} := by
  intro k _ G N hG
  let := N.isClosedImmersion
  obtain ⟨n, U, e, j, hj⟩ := (unipotent_iff_exists_embedding G).mp hG
  let := hj
  refine (unipotent_iff_exists_embedding (closedSubgroupAlgebraicGroup N)).mpr
    ⟨n, U, e, N.inclusion ≫ j, ?_⟩
  change IsClosedImmersion (N.inclusion.hom.hom.left ≫ j.hom.hom.left)
  infer_instance

section Coactions

variable {A B C : HopfAlgebraCategory k}
variable {V : Type u} [AddCommGroup V] [Module k V]

private lemma map_coaction_tensor
    (d : V →ₗ[k] V ⊗[k] A) (p : A →ₗ[k] B) (q : A →ₗ[k] C) (t : V ⊗[k] A) :
    (TensorProduct.map p q).lTensor V
        (TensorProduct.assoc k V A A (d.rTensor A t)) =
      TensorProduct.assoc k V B C (((p.lTensor V).comp d).rTensor C ((q.lTensor V) t)) := by
  induction t using TensorProduct.inductionOn with
  | tmul v a =>
    simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, LinearMap.comp_apply]
    generalize d v = s
    induction s using TensorProduct.inductionOn with
    | tmul w b => simp
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

private lemma coaction_tensor_counit (d : V →ₗ[k] V ⊗[k] A)
    (a : A ⟶ B) (x : V) :
    (Coalgebra.counit (R := k) (A := B)).lTensor V
        ((a.hom.toLinearMap.lTensor V) (d x)) =
      (Coalgebra.counit (R := k) (A := A)).lTensor V (d x) := by
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
  congr 2
  ext y
  exact CoalgHomClass.counit_comp_apply a.hom y

/-- Restriction along a group morphism by composition with its coordinate map. -/
private def restrictCoaction (a : A ⟶ B) (ρ : RightComodule k A V) :
    RightComodule k B V where
  coaction := (a.hom.toLinearMap.lTensor V).comp ρ.coaction
  coassoc x := by
    simp only [LinearMap.comp_apply]
    rw [← map_coaction_tensor, ρ.coassoc, ← LinearMap.lTensor_comp_apply,
      ← LinearMap.lTensor_comp_apply]
    have he : (TensorProduct.map a.hom.toLinearMap a.hom.toLinearMap).comp
          (Coalgebra.comul (R := k) (A := A)) =
        (Coalgebra.comul (R := k) (A := B)).comp a.hom.toLinearMap := by
      ext y
      exact CoalgHomClass.map_comp_comul_apply a.hom y
    rw [he]
  counit x := by
    rw [LinearMap.comp_apply, coaction_tensor_counit, ρ.counit]

private lemma invariants_restrict_eq (a : A ⟶ B) (ha : Function.Injective a.hom)
    (ρ : RightComodule k A V) :
    invariants B (restrictCoaction a ρ) = invariants A ρ := by
  ext x
  rw [invariant_iff_coaction, invariant_iff_coaction]
  have ht := Module.Flat.lTensor_preserves_injective_linearMap (M := V) a.hom.toLinearMap ha
  change (a.hom.toLinearMap.lTensor V) (ρ.coaction x) = x ⊗ₜ[k] (1 : B) ↔ _
  rw [← ht.eq_iff]
  rw [LinearMap.lTensor_tmul]
  change _ = _ ↔ _ = x ⊗ₜ[k] (a.hom 1)
  rw [map_one]

private def descendCoaction (a : A ⟶ B) (ha : Function.Injective a.hom)
    (ρ : RightComodule k B V) (d : V →ₗ[k] V ⊗[k] A)
    (hd : (a.hom.toLinearMap.lTensor V).comp d = ρ.coaction) : RightComodule k A V where
  coaction := d
  coassoc x := by
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := V) _
      (TensorProduct.map_injective_of_flat_flat _ _ ha ha)
    rw [map_coaction_tensor, hd, ← LinearMap.lTensor_comp_apply]
    have h : (TensorProduct.map a.hom.toLinearMap a.hom.toLinearMap).comp
          (Coalgebra.comul (R := k) (A := A)) =
        (Coalgebra.comul (R := k) (A := B)).comp a.hom.toLinearMap := by
      ext y
      exact CoalgHomClass.map_comp_comul_apply a.hom y
    rw [h, LinearMap.lTensor_comp_apply]
    have hdx : (a.hom.toLinearMap.lTensor V) (d x) = ρ.coaction x := DFunLike.congr_fun hd x
    rw [hdx]
    exact ρ.coassoc x
  counit x := by
    rw [← coaction_tensor_counit d a, ← LinearMap.comp_apply (a.hom.toLinearMap.lTensor V),
      ← LinearMap.comp_apply, hd, LinearMap.comp_apply, ρ.counit]

private theorem hasInvariantVectors_of_injective (a : A ⟶ B) (ha : Function.Injective a.hom)
    (hB : HasInvariantVectors B) : HasInvariantVectors A := by
  intro V _ _ _ _ ρ
  obtain ⟨v, hn, hv⟩ := hB V (restrictCoaction a ρ)
  exact ⟨v, hn, invariants_restrict_eq a ha ρ ▸ hv⟩

end Coactions

private lemma presentation_of_map (G Q : AffineAlgebraicGroup k) (p : G.val ⟶ Q.val) :
    ∃ (A B : HopfAlgebraCategory k) (a : A ⟶ B)
      (eG : specGroup B ≅ G.val) (eQ : specGroup A ≅ Q.val),
      specGroupMap a ≫ eQ.hom = eG.hom ≫ p := by
  obtain ⟨A, _, ⟨eQ⟩⟩ := groupPresentation Q
  obtain ⟨B, _, ⟨eG⟩⟩ := groupPresentation G
  let ff := hopfSpec.fullyFaithful (R := CommRingCat.of k)
  let a : A ⟶ B := (ff.preimage (eG.hom ≫ p ≫ eQ.inv)).unop
  have ha : specGroupMap a = eG.hom ≫ p ≫ eQ.inv := ff.map_preimage _
  exact ⟨A, B, a, eG, eQ, by rw [ha]; simp⟩

private lemma faithfullyFlat_of_presentation {G Q : GroupScheme k} (p : G ⟶ Q)
    {A B : HopfAlgebraCategory k} (a : A ⟶ B)
    (eG : specGroup B ≅ G) (eQ : specGroup A ≅ Q)
    (h : specGroupMap a ≫ eQ.hom = eG.hom ≫ p)
    (hf : Flat p.hom.hom.left) (hs : Surjective p.hom.hom.left) :
    a.hom.toAlgHom.toRingHom.FaithfullyFlat := by
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  have he := congrArg F.map h
  rw [F.map_comp, F.map_comp] at he
  have he' : F.map (specGroupMap a) = F.map eG.hom ≫ F.map p ≫ F.map eQ.inv := by
    simpa using congrArg (fun f ↦ f ≫ F.map eQ.inv) he
  apply (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom a.hom.toAlgHom.toRingHom)).mp
  change Flat (F.map (specGroupMap a)) ∧ Surjective (F.map (specGroupMap a))
  let : Flat (F.map p) := hf
  let : Surjective (F.map p) := hs
  rw [he']
  exact ⟨inferInstance, inferInstance⟩

theorem faithfullyFlatQuotientsUnipotent : FaithfullyFlatQuotientsUnipotent.{u} := by
  intro k _ G Q p hf hs hG
  obtain ⟨A, B, a, eG, eQ, h⟩ := presentation_of_map G Q p
  have hff := faithfullyFlat_of_presentation p a eG eQ h hf hs
  exact (unipotenceCriteria Q A eQ).1.mpr
    (hasInvariantVectors_of_injective a hff.injective ((unipotenceCriteria G B eG).1.mp hG))

section KernelInvariants

open Algebra.TensorProduct (includeLeft includeRight)

variable {A B : HopfAlgebraCategory k} (a : A ⟶ B)
variable [(Specs.kernelIdeal a).IsHopfIdeal k]

local notation "D" => hopfQuotient B (Specs.kernelIdeal a)
local notation "q" => CommHopfAlgCat.Hom.hom (hopfQuotientMap B (Specs.kernelIdeal a))
local notation "i" => CommHopfAlgCat.Hom.hom a

private lemma tensor_comul_eq_conv {S T U : HopfAlgebraCategory k}
    (p : S →ₐ[k] T) (r : S →ₐ[k] U) (x : S) :
    TensorProduct.map p.toLinearMap r.toLinearMap (Coalgebra.comul x) =
      (toConv (includeLeft.comp p) * toConv (includeRight.comp r)).ofConv x := by
  let f : S →ₐ[k] T ⊗[k] U := includeLeft.comp p
  let g : S →ₐ[k] T ⊗[k] U := includeRight.comp r
  change _ = (toConv f * toConv g) x
  rw [AlgHom.convMul_apply]
  have he : TensorProduct.map p.toLinearMap r.toLinearMap =
      (Algebra.TensorProduct.lift (includeLeft.comp p) (includeRight.comp r)
        (fun _ _ ↦ Commute.all ..)).toLinearMap := by
    ext y z
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  exact DFunLike.congr_fun he _

/-- The relative shear turns right kernel invariance into the faithfully flat equalizer equation. -/
private lemma right_coinvariants (hff : (i).toAlgHom.toRingHom.FaithfullyFlat) (x : B) :
    TensorProduct.map LinearMap.id (q).toLinearMap (Coalgebra.comul x) = x ⊗ₜ[k] (1 : D) ↔
      ∃ y : A, i y = x := by
  let P (b : A ⟶ B) : Prop :=
    let : Algebra A B := b.hom.toAlgHom.toRingHom.toAlgebra
    let : IsScalarTower k A B := IsScalarTower.of_algHom b.hom.toAlgHom
    ∃ e : B ⊗[A] B ≃ₐ[B] B ⊗[k] (B ⧸ Specs.kernelIdeal a),
      (e.toAlgHom.restrictScalars k).comp (includeRight.restrictScalars k) =
        (toConv ((includeLeft : B →ₐ[k] _).comp (𝟙 B : B ⟶ B).hom.toAlgHom) *
          toConv (includeRight.comp (Ideal.Quotient.mkₐ k (Specs.kernelIdeal a)))).ofConv
  have hs : P (a ≫ 𝟙 B) := exists_relativeShear a (𝟙 B)
  rw [Category.comp_id] at hs
  let : Algebra A B := (i).toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower k A B := IsScalarTower.of_algHom (i).toAlgHom
  let : Module.FaithfullyFlat A B := hff
  obtain ⟨e, he⟩ := hs
  have ht (z : B) : e (1 ⊗ₜ[A] z) =
      TensorProduct.map LinearMap.id (q).toLinearMap (Coalgebra.comul z) := by
    have h := tensor_comul_eq_conv (AlgHom.id k B) (q).toAlgHom z
    exact (DFunLike.congr_fun he z).trans h.symm
  have hu (z : B) : e (z ⊗ₜ[A] 1) = z ⊗ₜ[k] (1 : D) := e.commutes z
  rw [← ht, ← hu, e.injective.eq_iff]
  exact Iff.trans ⟨fun h ↦ sub_eq_zero.mpr h.symm, fun h ↦ (sub_eq_zero.mp h).symm⟩
    (Algebra.IsEffective.of_faithfullyFlat A B x)

private lemma left_comul_on_quotient (y : A) :
    TensorProduct.map (q).toLinearMap LinearMap.id (Coalgebra.comul (i y)) =
      (1 : D) ⊗ₜ[k] i y := by
  let L : WithConv (B →ₐ[k] D ⊗[k] B) := toConv (includeLeft.comp (q).toAlgHom)
  let R : WithConv (B →ₐ[k] D ⊗[k] B) := toConv includeRight
  let : Group (WithConv (A →ₐ[k] D ⊗[k] B)) :=
    convolutionGroup A (CommAlgCat.of k (D ⊗[k] B))
  have hL : toConv (L.ofConv.comp (i).toAlgHom) = (1 : WithConv (A →ₐ[k] D ⊗[k] B)) := by
    apply WithConv.ofConv_injective
    ext x
    change (includeLeft : D →ₐ[k] D ⊗[k] B) (q (i x)) = algebraMap k (D ⊗[k] B) (Coalgebra.counit x)
    rw [show q (i x) = algebraMap k D (Coalgebra.counit x) from
      DFunLike.congr_fun (kernelQuotientMap_comp a) x, AlgHom.commutes]
  have hprod : TensorProduct.map (q).toLinearMap LinearMap.id (Coalgebra.comul (i y)) =
      (L * R).ofConv (i y) := tensor_comul_eq_conv (q).toAlgHom (AlgHom.id k B) (i y)
  rw [hprod]
  have h := AlgHom.convMul_comp_bialgHom_distrib L R a.hom
  have hy := DFunLike.congr_fun h y
  change (L * R).ofConv (i y) =
    (toConv (L.ofConv.comp (i).toAlgHom) * toConv (R.ofConv.comp (i).toAlgHom)).ofConv y at hy
  rw [hL, one_mul] at hy
  exact hy

private lemma kernelInvariant_coaction {V : Type u} [AddCommGroup V] [Module k V]
    (hff : (i).toAlgHom.toRingHom.FaithfullyFlat) (ρ : RightComodule k B V)
    (w : kernelInvariants a ρ) :
    ρ.coaction w ∈ LinearMap.range ((i).toLinearMap.lTensor V) := by
  let f := (TensorProduct.map LinearMap.id (q).toLinearMap).comp
      (Coalgebra.comul (R := k) (A := B)) - (includeLeft : B →ₐ[k] B ⊗[k] D).toLinearMap
  have hex : Function.Exact (i).toLinearMap f := fun x ↦ by
    dsimp only [f, LinearMap.sub_apply, LinearMap.comp_apply]
    rw [sub_eq_zero]
    exact right_coinvariants a hff x
  apply (Module.Flat.lTensor_exact V hex (ρ.coaction w)).mp
  have hw := (invariant_iff_coaction D (restrictCoaction
    (hopfQuotientMap B (Specs.kernelIdeal a)) ρ) (w : V)).mp w.property
  change ((q).toLinearMap.lTensor V) (ρ.coaction w) = (w : V) ⊗ₜ[k] (1 : D) at hw
  have hmap := map_coaction_tensor ρ.coaction LinearMap.id (q).toLinearMap (ρ.coaction w)
  rw [ρ.coassoc, hw] at hmap
  rw [LinearMap.lTensor_id, LinearMap.id_comp, LinearMap.rTensor_tmul,
    ← LinearMap.lTensor_comp_apply] at hmap
  change (((TensorProduct.map LinearMap.id (q).toLinearMap).comp
    (Coalgebra.comul (R := k) (A := B)) - (includeLeft : B →ₐ[k] B ⊗[k] D).toLinearMap).lTensor V)
      (ρ.coaction w) = 0
  rw [LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero, hmap]
  generalize ρ.coaction w = t
  induction t using TensorProduct.inductionOn with
  | tmul v b => rfl
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]

private lemma kernelInvariants_isSubcomodule {V : Type u} [AddCommGroup V] [Module k V]
    (hff : (i).toAlgHom.toRingHom.FaithfullyFlat) (ρ : RightComodule k B V) :
    ρ.IsSubcomodule (kernelInvariants a ρ) := by
  let σ := restrictCoaction (hopfQuotientMap B (Specs.kernelIdeal a)) ρ
  let d := invariantDifference D σ
  have hex : Function.Exact (kernelInvariants a ρ).subtype d := fun x ↦ by
    change x ∈ kernelInvariants a ρ ↔ x ∈ LinearMap.range (kernelInvariants a ρ).subtype
    rw [Submodule.range_subtype]
  intro w
  apply (Module.Flat.rTensor_exact B hex (ρ.coaction w)).mp
  rw [show d = σ.coaction - trivialLinearMap D from rfl, LinearMap.rTensor_sub,
    LinearMap.sub_apply, sub_eq_zero]
  apply (TensorProduct.assoc k V D B).injective
  have hmap := map_coaction_tensor ρ.coaction (q).toLinearMap LinearMap.id (ρ.coaction w)
  have hid : (LinearMap.id : B →ₗ[k] B).lTensor V = LinearMap.id := by
    ext v b
    rfl
  rw [ρ.coassoc, hid, LinearMap.id_apply, ← LinearMap.lTensor_comp_apply] at hmap
  -- Applying the kernel to the first coefficient of the coproduct is trivial
  -- on all the descended coefficients.
  have hleft : ((TensorProduct.map (q).toLinearMap LinearMap.id).comp
      (Coalgebra.comul (R := k) (A := B))).comp (i).toLinearMap =
      (includeRight : B →ₐ[k] D ⊗[k] B).toLinearMap.comp (i).toLinearMap := by
    ext y
    exact left_comul_on_quotient a y
  have htriv (t : V ⊗[k] B) :
      TensorProduct.assoc k V D B ((trivialLinearMap D).rTensor B t) =
        ((includeRight : B →ₐ[k] D ⊗[k] B).toLinearMap.lTensor V) t := by
    induction t using TensorProduct.inductionOn with
    | tmul v b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  change TensorProduct.assoc k V D B
      (((((q).toLinearMap.lTensor V).comp ρ.coaction).rTensor B) (ρ.coaction w)) = _
  rw [← hmap, htriv]
  obtain ⟨t, ht⟩ := kernelInvariant_coaction a hff ρ w
  change ((i).toLinearMap.lTensor V) t = ρ.coaction w at ht
  rw [← ht, ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply, hleft]

theorem quotientActionOnKernelInvariants : QuotientActionOnKernelInvariants.{u} := by
  intro k _ A B a _ hff V _ _ ρ
  let W := kernelInvariants a ρ
  obtain ⟨σ, hσ⟩ := (RightComodule.isSubcomodule_iff_exists_coaction ρ W).mp
    (kernelInvariants_isSubcomodule a hff ρ)
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective W.subtype
    (LinearMap.ker_eq_bot.mpr W.subtype_injective)
  let j := a.hom.toLinearMap.lTensor W
  have hj : Function.Injective j :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := W) _ hff.injective
  have hrange (w : W) : σ.coaction w ∈ LinearMap.range j := by
    obtain ⟨t, ht⟩ := kernelInvariant_coaction a hff ρ w
    have h := DFunLike.congr_fun hσ w
    change W.subtype.rTensor B (σ.coaction w) = ρ.coaction w at h
    use r.rTensor A t
    change a.hom.toLinearMap.lTensor W (r.rTensor A t) = σ.coaction w
    rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply]
    change a.hom.toLinearMap.lTensor V t = ρ.coaction w at ht
    rw [ht, ← h, ← LinearMap.rTensor_comp_apply, hr, LinearMap.rTensor_id]
    rfl
  let d := (LinearEquiv.ofInjective j hj).symm.toLinearMap.comp
    (σ.coaction.codRestrict (LinearMap.range j) hrange)
  have hd : j.comp d = σ.coaction := by
    ext w
    exact congrArg Subtype.val ((LinearEquiv.ofInjective j hj).apply_symm_apply
      ⟨σ.coaction w, hrange w⟩)
  exact ⟨descendCoaction a hff.injective σ d hd, by
    change ((W.subtype.rTensor B).comp j).comp d = _
    rw [LinearMap.comp_assoc, hd, hσ]⟩

end KernelInvariants

private def kernel_presentation {G Q : GroupScheme k} (p : G ⟶ Q)
    (N : Specs.ClosedSubgroup G) (hN : Specs.IsSchemeKernel p N)
    {A B : HopfAlgebraCategory k} (a : A ⟶ B) [(Specs.kernelIdeal a).IsHopfIdeal k]
    (eG : specGroup B ≅ G) (eQ : specGroup A ≅ Q)
    (h : specGroupMap a ≫ eQ.hom = eG.hom ≫ p) :
    specGroup (hopfQuotient B (Specs.kernelIdeal a)) ≅ N.group := by
  let C := SchemeOver k
  let F := Grp.forget C
  let D := hopfQuotient B (Specs.kernelIdeal a)
  let j := specGroupMap (hopfQuotientMap B (Specs.kernelIdeal a))
  let e₀ : (specGroup (CommHopfAlgCat.of k k)).X ≅ 𝟙_ C :=
    Over.isoMk (Iso.refl (Spec (CommRingCat.of k))) (by
      change (𝟙 _) ≫ (𝟙 _) = Spec.map (𝟙 (CommRingCat.of k))
      rw [Spec.map_id, Category.comp_id])
  have ht := isTerminalTensorUnit (C := C)
  letI : IsMonHom e₀.hom := ⟨ht.hom_ext _ _, ht.hom_ext _ _⟩
  let eT : specGroup (CommHopfAlgCat.of k k) ≅ Grp.trivial C := Grp.mkIso' e₀
  let iQ : Grp.trivial C ⟶ Q := default
  let tN : N.group ⟶ Grp.trivial C := default
  let tD : specGroup D ⟶ Grp.trivial C := default
  have hN' : IsPullback N.inclusion tN p iQ := by
    apply IsPullback.of_map_of_faithful F
    change IsPullback N.inclusion.hom.hom tN.hom.hom p.hom.hom iQ.hom.hom
    have htN : tN.hom.hom = toUnit _ := ht.hom_ext _ _
    rw [htN]
    exact hN
  have hD : IsPullback (j ≫ eG.hom) tD p iQ :=
    (schemeKernel k a).1.of_iso
      (Iso.refl _) eG eT eQ (by simp [j]) (Subsingleton.elim _ _) h (by
        apply (cancel_epi eT.inv).mp
        exact Subsingleton.elim _ _)
  exact hD.isoIsPullback _ _ hN'

private lemma hasInvariantVectors_of_extension
    {A B : HopfAlgebraCategory k} (a : A ⟶ B) [(Specs.kernelIdeal a).IsHopfIdeal k]
    (hff : a.hom.toAlgHom.toRingHom.FaithfullyFlat)
    (hA : HasInvariantVectors A) (hN : HasInvariantVectors (hopfQuotient B (Specs.kernelIdeal a))) :
    HasInvariantVectors B := by
  intro V _ _ _ _ ρ
  let D := hopfQuotient B (Specs.kernelIdeal a)
  let q := hopfQuotientMap B (Specs.kernelIdeal a)
  let W := kernelInvariants a ρ
  obtain ⟨v, hv, hmem⟩ := hN V (restrictCoaction q ρ)
  let w : W := ⟨v, hmem⟩
  let : Nontrivial W := ⟨⟨w, 0, fun h ↦ hv (congrArg Subtype.val h)⟩⟩
  obtain ⟨σ, hσ⟩ := quotientActionOnKernelInvariants a hff ρ
  obtain ⟨z, hz, hzfix⟩ := hA W σ
  refine ⟨z.val, fun h ↦ hz (Subtype.ext h), (invariant_iff_coaction B ρ z.val).mpr ?_⟩
  have he := DFunLike.congr_fun hσ z
  rw [invariant_iff_coaction] at hzfix
  change W.subtype.rTensor B ((a.hom.toLinearMap.lTensor W) (σ.coaction z)) =
    ρ.coaction z.val at he
  rw [hzfix, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul] at he
  rw [show a.hom.toLinearMap (1 : A) = (1 : B) from map_one a.hom] at he
  exact he.symm

theorem extensionsUnipotent : ExtensionsUnipotent.{u} := by
  intro k _ G Q p N hN hf hs huN huQ
  obtain ⟨A, B, a, eG, eQ, h⟩ := presentation_of_map G Q p
  let : (Specs.kernelIdeal a).IsHopfIdeal k := hopfKernelIdeal k a
  let H := closedSubgroupAlgebraicGroup N
  have eN : specGroup (hopfQuotient B (Specs.kernelIdeal a)) ≅ H.val :=
    kernel_presentation p N hN a eG eQ h
  exact (unipotenceCriteria G B eG).1.mpr
    (hasInvariantVectors_of_extension a (faithfullyFlat_of_presentation p a eG eQ h hf hs)
      ((unipotenceCriteria Q A eQ).1.mp huQ) ((unipotenceCriteria H _ eN).1.mp huN))

private lemma coalgebraFiltration_baseChange {A : HopfAlgebraCategory k}
    (K : Type u) [Field K] [Algebra k K] (hA : HasCoalgebraFiltration A) :
    HasCoalgebraFiltration (scalarExtension A K) := by
  obtain ⟨C, hC, hex, h0, hΔ⟩ := hA
  let B := scalarExtension A K
  let F : ℕ → Submodule K B := fun n ↦ (C n).baseChange K
  have hF : Monotone F := fun _ _ h ↦ Submodule.baseChange_mono K (hC h)
  refine ⟨F, hF, ?_, ?_, ?_⟩
  · intro x
    change ∃ n, x ∈ F n
    induction x using TensorProduct.inductionOn with
    | tmul b a =>
      obtain ⟨n, hn⟩ := hex a
      exact ⟨n, Submodule.tmul_mem_baseChange_of_mem b hn⟩
    | add x y hx hy =>
      obtain ⟨m, hm⟩ := hx
      obtain ⟨n, hn⟩ := hy
      exact ⟨max m n, (F _).add_mem (hF (le_max_left m n) hm) (hF (le_max_right m n) hn)⟩
  · change (C 0).baseChange K = _
    rw [h0, Submodule.baseChange_span, Set.image_singleton]
    rfl
  · intro n
    let e := TensorProduct.AlgebraTensorModule.distribBaseChange k K A A
    let l : A ⊗[k] A →ₗ[k] B ⊗[K] B :=
      (e.toLinearMap.restrictScalars k).comp (TensorProduct.mk k K (A ⊗[k] A) 1)
    have hl (x y : A) : l (x ⊗ₜ[k] y) = ((1 : K) ⊗ₜ[k] x) ⊗ₜ[K] ((1 : K) ⊗ₜ[k] y) := rfl
    have hc (x : A) : Coalgebra.comul (R := K) (A := B) ((1 : K) ⊗ₜ[k] x) =
        l (Coalgebra.comul (R := k) x) := by
      rw [TensorProduct.comul_tmul, Bialgebra.comul_one]
      generalize Coalgebra.comul (R := k) x = t
      induction t using TensorProduct.inductionOn with
      | tmul x y =>
        rw [hl]
        rfl
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    have hmaps : tensorFiltration C n ≤ ((tensorFiltration F n).restrictScalars k).comap l := by
      apply iSup_le
      intro j t ht
      obtain ⟨t, rfl⟩ := ht
      induction t using TensorProduct.inductionOn with
      | tmul x y =>
        change l ((x : A) ⊗ₜ[k] (y : A)) ∈ tensorFiltration F n
        rw [hl]
        exact tmul_mem_tensorFiltration hF (show j.val + (n - j.val) ≤ n by omega)
          (Submodule.tmul_mem_baseChange_of_mem 1 x.property)
          (Submodule.tmul_mem_baseChange_of_mem 1 y.property)
      | add x y hx hy =>
        rw [map_add]
        exact Submodule.add_mem _ hx hy
    have hle : F n ≤ (tensorFiltration F n).comap (Coalgebra.comul (R := K)) := by
      change (C n).baseChange K ≤ _
      rw [Submodule.baseChange_eq_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨a, ha, rfl⟩
      change Coalgebra.comul (R := K) (A := B) ((1 : K) ⊗ₜ[k] a) ∈ tensorFiltration F n
      rw [hc]
      exact hmaps (hΔ n a ha)
    exact fun _ hx ↦ hle hx

private lemma hasInvariantVectors_of_baseChange {A : HopfAlgebraCategory k}
    (K : Type u) [Field K] [Algebra k K]
    (hA : HasInvariantVectors (scalarExtension A K)) : HasInvariantVectors A := by
  intro V _ _ _ _ ρ
  let b : Module.Basis (Index.{u} (Module.finrank k V)) k V :=
    (Module.finBasis k V).reindex Equiv.ulift.symm
  let : Nontrivial (K ⊗[k] V) :=
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_right k K V
      (Algebra.linearMap k K) (algebraMap k K).injective
  obtain ⟨σ, _, hσ, _⟩ := fieldExtensionComparison (K := K) A b ρ
  obtain ⟨v, hv, hmem⟩ := hA (K ⊗[k] V) σ
  by_contra! h
  have hz : invariants A ρ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    exact fun w hw ↦ by_contra fun hn ↦ h w hn hw
  rw [hσ, hz, Submodule.baseChange_bot, Submodule.mem_bot] at hmem
  exact hv hmem

theorem unipotenceFieldExtension : UnipotenceFieldExtension.{u} := by
  intro k K _ _ _ G
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation G
  let G' := baseChangedAlgebraicGroup K G
  let B := scalarExtension A K
  have e' : specGroup B ≅ G'.val :=
    extendedGroupIso K A ≪≫ (groupBaseChange k K).mapIso e
  change IsUnipotent G' ↔ IsUnipotent G
  obtain ⟨hG, hI, hE, hC⟩ := unipotenceCriteria G A e
  have hG' := (unipotenceCriteria G' B e').1
  exact ⟨fun h ↦ hG.mpr (hasInvariantVectors_of_baseChange K (hG'.mp h)),
    fun h ↦ hG'.mpr (hasInvariantVectors_of_filtration
      (coalgebraFiltration_baseChange K ((hI.trans (hE.trans hC)).mp (hG.mp h))))⟩

end

end LinearAlgebraicGroups.Unipotent
