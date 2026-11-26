import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.OrderedRootProducts
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterOpenCell
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Ideal.Cotangent

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj LaurentPolynomial

universe u

namespace LinearAlgebraicGroups.RootData.OrderedRootProducts

open _root_.LinearAlgebraicGroups.Specs
open Specs.AbstractPairing (Root)
open Specs.BorelsAndChambers (BorelsThroughT GeometricBorelChamberConjugacy
  GeometricBorelRootSubgroups PositiveSystemsFromCocharacters RegularCocharacterBorel
  contractingSubgroup positiveRoots)
open Specs.CharacterDescent (Cocharacter)
open Specs.CharacterPairing (absoluteRoots characterValue pairing)
open Specs.GeometricRadicals (IsReductive IsSplitTorus IsUnipotentRadical)
open Specs.RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open Specs.RootGroups (AdditiveLine HasScalarAction RootSubgroups RootDimension rootPoint)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.OrderedRootProducts
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open _root_.LinearAlgebraicGroups.RootData.RootGroups (rootDimension rootSubgroups)
open CocharacterDynamics
open private affine_subgroup pointHom subgroupInclusionFactors
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private affinePointEquiv
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

variable {k : Type u} [Field k]

private abbrev underlying (k : Type u) [Field k] := Grp.forget (SchemeOver k)

private theorem inclusion_mono {G : GroupScheme k} (A : ClosedSubgroup G) :
    Mono A.inclusion := by
  letI := A.isClosedImmersion
  letI : Mono A.inclusion.hom.hom := Over.mono_of_mono_left _
  exact (underlying k).mono_of_mono_map (show Mono A.inclusion.hom.hom from inferInstance)

private def subgroupIso {G : GroupScheme k} {A B : ClosedSubgroup G}
    (h : SameSubgroup A B) :
    {e : A.group ≅ B.group // e.hom ≫ B.inclusion = A.inclusion} := by
  let f := Classical.choose h.1
  let g := Classical.choose h.2
  have hf : f ≫ B.inclusion = A.inclusion := Classical.choose_spec h.1
  have hg : g ≫ A.inclusion = B.inclusion := Classical.choose_spec h.2
  letI := inclusion_mono A
  letI := inclusion_mono B
  exact ⟨⟨f, g, by apply (cancel_mono A.inclusion).mp; simp [Category.assoc, hg, hf],
    by apply (cancel_mono B.inclusion).mp; simp [Category.assoc, hf, hg]⟩, hf⟩

private theorem normal_postcompose_iso {H G G' : GroupScheme k}
    (i : H ⟶ G) (e : G ≅ G') (h : IsNormalSubgroup i) :
    IsNormalSubgroup (i ≫ e.hom) := by
  obtain ⟨c, hc⟩ := h
  let a : G'.X ⊗ H.X ⟶ G.X ⊗ H.X := e.inv.hom.hom ⊗ₘ 𝟙 H.X
  refine ⟨a ≫ c, ?_⟩
  change (a ≫ c) ≫ i.hom.hom ≫ e.hom.hom.hom = _
  rw [← Category.assoc, Category.assoc a, hc]
  have he : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ :=
    ((underlying k).mapIso e).inv_hom_id
  simp only [subgroupConjugation, MonObj.mul_comp, GrpObj.inv_comp, MonObj.comp_mul,
    GrpObj.comp_inv, ← Category.assoc, show a ≫ fst G.X H.X =
      fst G'.X H.X ≫ e.inv.hom.hom from tensorHom_fst _ _,
    show a ≫ snd G.X H.X = snd G'.X H.X from by simp [a]]
  simp only [Category.assoc, he, Category.comp_id]
  rfl

private def pushSubgroup {G G' : GroupScheme k} (e : G ≅ G') (H : ClosedSubgroup G) :
    ClosedSubgroup G' := by
  refine ⟨H.group, H.inclusion ≫ e.hom, ?_⟩
  letI := H.isClosedImmersion
  haveI : IsIso e.hom.hom.hom.left := inferInstanceAs
    (IsIso ((underlying k ⋙ Over.forget _).map e.hom))
  change IsClosedImmersion (H.inclusion.hom.hom.left ≫ e.hom.hom.hom.left)
  exact IsClosedImmersion.comp _ _

private theorem radical_transport
    {A B : AffineAlgebraicGroup k} (e : A.val ≅ B.val)
    (H : ClosedSubgroup A.val) (h : IsUnipotentRadical A H) :
    IsUnipotentRadical B (pushSubgroup e H) := by
  refine ⟨⟨h.1.1, h.1.2.1, normal_postcompose_iso _ e h.1.2.2⟩, h.2.1, ?_⟩
  intro S hS hU
  obtain ⟨j, hj⟩ := h.2.2 (pushSubgroup e.symm S)
    ⟨hS.1, hS.2.1, normal_postcompose_iso _ e.symm hS.2.2⟩ hU
  refine ⟨j, ?_⟩
  change j ≫ H.inclusion ≫ e.hom = S.inclusion
  rw [← Category.assoc, hj]
  change (S.inclusion ≫ e.inv) ≫ e.hom = S.inclusion
  simp

private theorem contractingProduct_exists
    (hDimension : RootDimension.{u}) (hRoots : RootSubgroups.{u})
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group) (hmax : IsGeometricallyMaximal T) :
    (absoluteRoots T).Finite ∧ Nonempty (RootSubgroupFamily T) ∧
      ∀ cochar : Cocharacter T.group, Nonempty (LimitDecomposition (cochar ≫ T.inclusion)) := by
  refine ⟨(hDimension G hG T hT hmax).1, ?_, fun cochar => existsLimitDecomposition G _⟩
  have h : ∀ α : Root T, ∃ U : ClosedSubgroup G.val, Specs.RootGroups.IsRootSubgroup T U α.val := by
    intro α
    obtain ⟨U, hU, _⟩ := ((hRoots G hG T hT hmax).2 α.val α.property).2.2
    exact ⟨U, hU⟩
  exact ⟨fun α => ⟨Classical.choose (h α), Classical.choose_spec (h α)⟩⟩

private theorem rootPoint_map {A : AdditiveLine k} {J : GroupScheme k}
    (x : A.group ⟶ J) {R S : TestAlgebra k} (f : R ⟶ S) (a : R) :
    mapPoints f (rootPoint x R a) = rootPoint x S (f.hom a) := by
  unfold mapPoints rootPoint
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp]
  congr 2
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  exact (Polynomial.aeval_algHom f.hom a).symm

private theorem rootPoint_zero {A : AdditiveLine k} {J : GroupScheme k}
    (x : A.group ⟶ J) (R : TestAlgebra k) : rootPoint x R 0 = 1 := by
  letI := A.operations.hopf
  let B : HopfAlgebraCategory k := CommHopfAlgCat.of k (Polynomial k)
  let f : B →ₐ[k] R := Polynomial.aeval 0
  have hf : f = (Algebra.ofId k R).comp (Bialgebra.counitAlgHom k B) := by
    apply Polynomial.algHom_ext
    change Polynomial.aeval 0 Polynomial.X =
      algebraMap k R (A.operations.epsilon Polynomial.X)
    simp [A.counit]
  have h : (hopfSpecPointIso B).hom.app R (WithConv.toConv f) =
      (1 : GroupPoints A.group R) := by
    rw [hf]
    exact map_one ((hopfSpecPointIso B).hom.app R).hom
  change ((hopfSpecPointIso B).hom.app R (WithConv.toConv f) : GroupPoints A.group R) ≫
    x.hom.hom = 1
  rw [h, MonObj.one_comp]

private theorem rootPoint_surjective {A : AdditiveLine k} {J : GroupScheme k}
    (x : A.group ≅ J) (R : TestAlgebra k) :
    Function.Surjective (rootPoint x.hom R) := by
  intro p
  let P := CommAlgCat.of k (Polynomial k)
  let e : (testSpec k).obj (op P) ≅ A.group.X := Iso.refl _
  let f := (affinePointEquiv e R).symm (p ≫ x.inv.hom.hom)
  have hf : Polynomial.aeval (f Polynomial.X) = f :=
    Polynomial.algHom_ext (Polynomial.aeval_X _)
  refine ⟨f Polynomial.X, ?_⟩
  unfold rootPoint
  rw [show (Polynomial.aeval (f Polynomial.X) : Polynomial k →ₐ[k] R) = f from hf]
  have h := (affinePointEquiv e R).apply_symm_apply (p ≫ x.inv.hom.hom)
  change (testSpec k).map (CommAlgCat.ofHom f).op ≫ 𝟙 _ = p ≫ x.inv.hom.hom at h
  rw [Category.comp_id] at h
  rw [h, Category.assoc]
  change p ≫ ((underlying k).mapIso x).inv ≫ ((underlying k).mapIso x).hom = p
  rw [Iso.inv_hom_id, Category.comp_id]

private theorem rootPoint_hasLimit
    {G : GroupScheme k} {T : ClosedSubgroup G} {A : AdditiveLine k}
    {α : Specs.CharacterDescent.Character T.group} {x : A.group ⟶ G}
    (hx : HasScalarAction T α x) (cochar : Cocharacter T.group)
    (hpos : 0 < pairing T.group α cochar) (R : TestAlgebra k) (a : R) :
    HasLimit (cochar ≫ T.inclusion) (rootPoint x R a) 1 := by
  let n := (pairing T.group α cochar).toNat
  have hn : (n : ℤ) = pairing T.group α cochar := Int.toNat_of_nonneg hpos.le
  have hn0 : n ≠ 0 := by omega
  let b : Polynomial R := Polynomial.C a * Polynomial.X ^ n
  refine ⟨rootPoint x (polynomialAlgebra R) b, ?_, ?_⟩
  · rw [rootPoint_map]
    let S := laurentAlgebra R
    let t := cocharacterPoint cochar S (laurentParameter R)
    have h := hx S t ((laurentConstants R).hom a)
    dsimp only at h
    have hχ : characterValue α S t = (↑(laurentParameter R ^ n) : S) := by
      rw [(CharacterPairing.characterPairingComposition T.group α cochar).2, ← hn, zpow_natCast]
    have hco : cocharacterPoint (cochar ≫ T.inclusion) S (laurentParameter R) =
        t ≫ T.inclusion.hom.hom := by
      unfold cocharacterPoint
      dsimp only [t]
      rw [Functor.map_comp, NatTrans.comp_app]
      rfl
    change _ = orbit (cochar ≫ T.inclusion) (rootPoint x R a)
    unfold orbit
    rw [hco, rootPoint_map, h, hχ]
    congr 1
    change (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R) b =
      ((laurentParameter R).val ^ n) * LaurentPolynomial.C a
    simp only [b, map_mul, map_pow, Polynomial.toLaurent_C, Polynomial.toLaurent_X]
    exact mul_comm _ _
  · rw [rootPoint_map]
    have h : (polynomialEvaluate R 0).hom b = 0 := by
      change Polynomial.aevalTower (AlgHom.id k R) (0 : R) b = 0
      simp [b, hn0]
    rw [h, rootPoint_zero]

private theorem rootProduct_factors {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    {U : RootSubgroupFamily T} {c : Cocharacter G.val} (D : LimitDecomposition c) :
    ∀ (l : List (Root T)), (∀ α ∈ l, IsSubgroupOf (U α).val D.contracting) →
      ∃ p : product (fun α => (U α).val.group.X) l ⟶ D.contracting.group.X,
        p ≫ D.contracting.inclusion.hom.hom = rootProduct U l
  | [], _ => ⟨1, MonObj.one_comp D.contracting.inclusion.hom.hom⟩
  | α :: l, h => by
    obtain ⟨j, hj⟩ := h α (List.mem_cons_self)
    obtain ⟨p, hp⟩ := rootProduct_factors D l (fun β hβ => h β (List.mem_cons_of_mem _ hβ))
    refine ⟨(fst _ _ ≫ j.hom.hom) * (snd _ _ ≫ p), ?_⟩
    have hj' : j.hom.hom ≫ D.contracting.inclusion.hom.hom = (U α).val.inclusion.hom.hom :=
      congrArg (underlying k).map hj
    simp only [rootProduct, MonObj.mul_comp, Category.assoc, hj', hp]


section CoordinateAlgebra

variable {k : Type*} [Field k] {A B : Type*} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]

private abbrev augmentationIdeal (e : A →ₐ[k] k) := RingHom.ker e.toRingHom

private theorem coeff_mul_induction (e : A →ₐ[k] k) (δ : A →ₐ[k] Polynomial A)
    (hzero : ∀ x, (δ x).coeff 0 = algebraMap k A (e x)) (n : ℕ)
    (J : Ideal A) (Q : Subring A)
    (hsmall : ∀ j < n, ∀ x ∈ augmentationIdeal e, ∀ y ∈ J,
      (δ x).coeff j * (δ y).coeff (n - j) ∈ Q)
    (hJ : J ≤ augmentationIdeal e)
    (z : A) (hz : z ∈ augmentationIdeal e * J) :
    (δ z).coeff n ∈ Q := by
  refine Submodule.mul_induction_on hz ?_ ?_
  · intro x hx y hy
    have hx₀ : (δ x).coeff 0 = 0 := by
      rw [hzero, show e x = 0 from hx, map_zero]
    have hy₀ : (δ y).coeff 0 = 0 := by
      rw [hzero, show e y = 0 from hJ hy, map_zero]
    rw [map_mul, Polynomial.coeff_mul]
    apply Subring.sum_mem
    intro p hp
    have hp' := Finset.mem_antidiagonal.mp hp
    by_cases hx' : p.1 = 0
    · simp [hx', hx₀]
    by_cases hy' : p.2 = 0
    · simp [hy', hy₀]
    have hn' : p.1 < n := by omega
    have he : n - p.1 = p.2 := by omega
    rw [← he]
    exact hsmall p.1 hn' x hx y hy
  · intro x y hx hy
    rw [map_add, Polynomial.coeff_add]
    exact Q.add_mem hx hy

/-- Coefficients of the square of the augmentation ideal are sums of products
of lower positive degrees. Cotangent surjectivity therefore lifts every coefficient. -/
private theorem contractionSurjective (eA : A →ₐ[k] k) (eB : B →ₐ[k] k)
    (δA : A →ₐ[k] Polynomial A) (δB : B →ₐ[k] Polynomial B)
    (f : A →ₐ[k] B) (hf : eB.comp f = eA)
    (hzero : ∀ b, (δB b).coeff 0 = algebraMap k B (eB b))
    (hone : ∀ b, (δB b).eval 1 = b)
    (hδ : ∀ a n, (δB (f a)).coeff n = f ((δA a).coeff n))
    (h : Function.Surjective (Ideal.mapCotangent (augmentationIdeal eA)
      (augmentationIdeal eB) f (by
        intro a ha
        exact (DFunLike.congr_fun hf a).trans (show eA a = 0 from ha)))) :
    Function.Surjective f := by
  let J := augmentationIdeal eB
  let Q := f.toRingHom.range
  have hb (n : ℕ) : ∀ b : B, (δB b).coeff n ∈ Q := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro b
      let b' : J := ⟨b - algebraMap k B (eB b), by
        change eB (_ - _) = 0
        rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]⟩
      obtain ⟨q, hq⟩ := h (J.toCotangent b')
      obtain ⟨a, rfl⟩ := (augmentationIdeal eA).toCotangent_surjective q
      change J.toCotangent ⟨f a.val, _⟩ = J.toCotangent b' at hq
      rw [eq_comm, ← sub_eq_zero, ← map_sub] at hq
      have hrem : b - algebraMap k B (eB b) - f a.val ∈ J * J := by
        rw [← pow_two]
        exact J.mem_toCotangent_ker.mp hq
      let c := algebraMap k A (eB b) + a.val
      have hs : b = f c + (b - algebraMap k B (eB b) - f a.val) := by
        rw [map_add, AlgHom.commutes]
        ring
      have hc : (δB (f c)).coeff n ∈ Q :=
        ⟨_, (hδ c n).symm⟩
      rw [hs, map_add, Polynomial.coeff_add]
      refine Q.add_mem hc (coeff_mul_induction eB δB hzero n J Q ?_ le_rfl _ hrem)
      intro j hj x hx y hy
      have hj' : n - j < n ∨ j = 0 := by omega
      rcases hj' with hj' | rfl
      · exact Q.mul_mem (ih j hj x) (ih _ hj' y)
      · rw [hzero, show eB x = 0 from hx, map_zero, zero_mul]
        exact Q.zero_mem
  intro b
  change b ∈ Q
  rw [← hone b, Polynomial.eval_eq_sum_range]
  simpa only [one_pow, mul_one] using Q.sum_mem (fun n _ => hb n b :
    ∀ n ∈ Finset.range ((δB b).natDegree + 1), (δB b).coeff n ∈ Q)

/-- A section of the coordinate map gives a projection onto its kernel.
Cotangent injectivity makes that kernel equal to its product with the augmentation
ideal, and contraction then makes each of its coefficients vanish. -/
private theorem contractionInjective (eA : A →ₐ[k] k) (eB : B →ₐ[k] k)
    (δA : A →ₐ[k] Polynomial A)
    (f : A →ₐ[k] B) (hf : eB.comp f = eA)
    (hzero : ∀ a, (δA a).coeff 0 = algebraMap k A (eA a))
    (hone : ∀ a, (δA a).eval 1 = a)
    (h : Function.Injective (Ideal.mapCotangent (augmentationIdeal eA)
      (augmentationIdeal eB) f (by
        intro a ha
        exact (DFunLike.congr_fun hf a).trans (show eA a = 0 from ha))))
    (s : B →ₐ[k] A) (hs : f.comp s = AlgHom.id k B) :
    Function.Injective f := by
  let J := augmentationIdeal eA
  let K := RingHom.ker f.toRingHom
  have hfs : ∀ b, f (s b) = b := DFunLike.congr_fun hs
  have hK : K ≤ J := by
    intro a ha
    change eA a = 0
    rw [← hf, AlgHom.comp_apply, show f a = 0 from ha, map_zero]
  have hK₂ : K ≤ J ^ 2 := by
    intro a ha
    have ha' : a ∈ J := hK ha
    refine J.mem_toCotangent_ker.mp (show J.toCotangent ⟨a, ha'⟩ = 0 from h ?_)
    rw [map_zero]
    change (augmentationIdeal eB).toCotangent ⟨f a, _⟩ = 0
    exact congrArg (fun z : augmentationIdeal eB => (augmentationIdeal eB).toCotangent z)
      (Subtype.ext (show f a = 0 from ha))
  let P := LinearMap.id (R := k) (M := A) - s.toLinearMap.comp f.toLinearMap
  have hP (a : A) : P a ∈ K := by
    change f (a - s (f a)) = 0
    rw [map_sub, hfs, sub_self]
  have hm (a : A) (ha : a ∈ J ^ 2) : P a ∈ J * K := by
    rw [pow_two] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro x hx y hy
      have hsf : s (f y) ∈ J := by
        change eA _ = 0
        rw [← hf, AlgHom.comp_apply, hfs]
        exact (DFunLike.congr_fun hf y).trans (RingHom.mem_ker.mp hy)
      have he : P (x * y) = x * P y + s (f y) * P x := by
        change x * y - s (f (x * y)) = x * (y - s (f y)) + s (f y) * (x - s (f x))
        rw [map_mul, map_mul]
        ring
      rw [he]
      exact (J * K).add_mem (Ideal.mul_mem_mul hx (hP y)) (Ideal.mul_mem_mul hsf (hP x))
    · intro x y hx hy
      rw [map_add]
      exact (J * K).add_mem hx hy
  have hmul : K ≤ J * K := by
    intro a ha
    have hPa : P a = a := by
      change a - s (f a) = a
      rw [show f a = 0 from ha, map_zero, sub_zero]
    exact hPa ▸ hm a (hK₂ ha)
  have hnil (n : ℕ) : ∀ a ∈ K, (δA a).coeff n = 0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a ha
      have hsupp (a : A) (ha : a ∈ J * K) : (δA a).coeff n = 0 := by
        refine Submodule.mul_induction_on ha ?_ ?_
        · intro x hx y hy
          rw [map_mul, Polynomial.coeff_mul]
          apply Finset.sum_eq_zero
          intro p hp
          have hp' := Finset.mem_antidiagonal.mp hp
          by_cases h0 : p.1 = 0
          · rw [h0, hzero, show eA x = 0 from hx, map_zero, zero_mul]
          · rw [ih p.2 (by omega) y hy, mul_zero]
        · intro x y hx hy
          rw [map_add, Polynomial.coeff_add, hx, hy, add_zero]
      exact hsupp a (hmul ha)
  apply (injective_iff_map_eq_zero f.toLinearMap).mpr
  intro a ha
  have ha' : a ∈ K := ha
  rw [← hone a]
  have hh : δA a = 0 := Polynomial.ext fun n => by rw [hnil n a ha', Polynomial.coeff_zero]
  rw [hh, Polynomial.eval_zero]


end CoordinateAlgebra

private structure RootCoordinate {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    (U : RootSubgroupFamily T) (α : Root T) where
  line : AdditiveLine k
  iso : line.group ≅ (U α).val.group
  scalar : HasScalarAction T α.val (iso.hom ≫ (U α).val.inclusion)
  tangentRange : Set.range (mapPointKernel (U α).val.inclusion) =
    Specs.CharacterPairing.adjointWeightVectors T α.val

private theorem rootCoordinate_exists (hRoots : RootSubgroups.{u}) (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group)
    (hmax : IsGeometricallyMaximal T) (U : RootSubgroupFamily T) (α : Root T) :
    Nonempty (RootCoordinate U α) := by
  obtain ⟨V, _, _, hV, ⟨A, x, hx⟩, unique⟩ :=
    ((hRoots G hG T hT hmax).2 α.val α.property).2.2
  let e := subgroupIso (unique (U α).val (U α).property)
  refine ⟨⟨A, x ≪≫ e.val, ?_, ?_⟩⟩
  · change HasScalarAction T α.val ((x.hom ≫ e.val.hom) ≫ (U α).val.inclusion)
    rw [Category.assoc, e.property]
    exact hx
  · rw [← hV]
    have hi : e.val.inv ≫ V.inclusion = (U α).val.inclusion := by
      calc
        e.val.inv ≫ V.inclusion = e.val.inv ≫ (e.val.hom ≫ (U α).val.inclusion) :=
          congrArg (fun j => e.val.inv ≫ j) e.property.symm
        _ = (U α).val.inclusion := Iso.inv_hom_id_assoc _ _
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨mapPointKernel e.val.inv q, by
        apply Subtype.ext
        change (q.toMul.val ≫ (underlying k).map e.val.inv) ≫ (underlying k).map V.inclusion =
          q.toMul.val ≫ (underlying k).map (U α).val.inclusion
        rw [Category.assoc, ← Functor.map_comp, hi]⟩
    · rintro ⟨q, rfl⟩
      exact ⟨mapPointKernel e.val.hom q, by
        apply Subtype.ext
        change (q.toMul.val ≫ (underlying k).map e.val.hom) ≫
          (underlying k).map (U α).val.inclusion = q.toMul.val ≫ (underlying k).map V.inclusion
        rw [Category.assoc, ← Functor.map_comp, e.property]⟩

private theorem rootSubgroup_embeds {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    {U : RootSubgroupFamily T} {α : Root T} (x : RootCoordinate U α)
    (cochar : Cocharacter T.group) (D : LimitDecomposition (cochar ≫ T.inclusion))
    (hα : α ∈ positiveRoots T cochar) : IsSubgroupOf (U α).val D.contracting := by
  refine subgroupInclusionFactors (affine_subgroup G.property.1 _) D.contracting
    (U α).val.inclusion ?_
  intro R p
  obtain ⟨a, rfl⟩ := rootPoint_surjective x.iso R p
  apply (D.contracting_points R _).mp
  exact rootPoint_hasLimit x.scalar cochar hα R a

private theorem rootPoint_injective {A : AdditiveLine k} {J : GroupScheme k}
    (x : A.group ≅ J) (R : TestAlgebra k) :
    Function.Injective (rootPoint x.hom R) := by
  intro a b hab
  letI : IsIso x.hom.hom.hom := inferInstanceAs (IsIso ((underlying k).map x.hom))
  unfold rootPoint at hab
  have h := (cancel_mono x.hom.hom.hom).mp hab
  have hh := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective h
  exact (Polynomial.aeval_X a).symm.trans
    ((congrArg (fun f => f.unop.hom Polynomial.X) hh).trans (Polynomial.aeval_X b))

section ProductPoints

variable {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val} {U : RootSubgroupFamily T}

private abbrev ProductScheme (U : RootSubgroupFamily T) (l : List (Root T)) :=
  product (fun α => (U α).val.group.X) l

/-- On test algebras a choice of one additive coordinate per root gives the
ordered product point. Only the coordinates belonging to the list are used. -/
private def productPoint (x : ∀ α, RootCoordinate U α) (R : TestAlgebra k)
    (a : Root T → R) : (l : List (Root T)) → Points (ProductScheme U l) R
  | [] => toUnit _
  | α :: l => lift (rootPoint (x α).iso.hom R (a α)) (productPoint x R a l)

private theorem productPoint_map (x : ∀ α, RootCoordinate U α) {R S : TestAlgebra k}
    (f : R ⟶ S) (a : Root T → R) (l : List (Root T)) :
    mapPoints f (productPoint x R a l) = productPoint x S (fun α => f.hom (a α)) l := by
  induction l with
  | nil => exact toUnit_unique _ _
  | cons α l ih =>
    apply CartesianMonoidalCategory.hom_ext
    · change (testSpec k).map f.op ≫
          lift (rootPoint (x α).iso.hom R (a α)) (productPoint x R a l) ≫ fst _ _ = _
      simp only [lift_fst, productPoint]
      exact rootPoint_map _ f _
    · change (testSpec k).map f.op ≫
          lift (rootPoint (x α).iso.hom R (a α)) (productPoint x R a l) ≫ snd _ _ = _
      simpa only [lift_snd, productPoint] using ih

private theorem productPoint_eq_iff (x : ∀ α, RootCoordinate U α) (R : TestAlgebra k)
    (a b : Root T → R) (l : List (Root T)) :
    productPoint x R a l = productPoint x R b l ↔ ∀ α ∈ l, a α = b α := by
  induction l with
  | nil => exact ⟨fun _ _ h => False.elim (List.not_mem_nil h), fun _ => toUnit_unique _ _⟩
  | cons α l ih =>
    constructor
    · intro h β hβ
      have hfst := congrArg (fun q : Points (ProductScheme U (α :: l)) R => q ≫ fst _ _) h
      have hsnd := congrArg (fun q : Points (ProductScheme U (α :: l)) R => q ≫ snd _ _) h
      simp only [productPoint, lift_fst] at hfst
      simp only [productPoint, lift_snd] at hsnd
      rcases List.mem_cons.mp hβ with rfl | hβ
      · exact rootPoint_injective (x β).iso R hfst
      · exact ih.mp hsnd β hβ
    · intro h
      apply CartesianMonoidalCategory.hom_ext
      · simp only [productPoint, lift_fst, h α List.mem_cons_self]
      · simp only [productPoint, lift_snd]
        exact ih.mpr (fun β hβ => h β (List.mem_cons_of_mem _ hβ))

private theorem productPoint_surjective (x : ∀ α, RootCoordinate U α) (R : TestAlgebra k)
    (l : List (Root T)) (hl : l.Nodup) :
    Function.Surjective (fun a : Root T → R => productPoint x R a l) := by
  classical
  induction l with
  | nil => exact fun p => ⟨0, toUnit_unique _ _⟩
  | cons α l ih =>
    intro p
    obtain ⟨a, ha⟩ := rootPoint_surjective (x α).iso R (p ≫ fst _ _)
    obtain ⟨b, hb⟩ := ih hl.of_cons (p ≫ snd _ _)
    refine ⟨Function.update b α a, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [productPoint, lift_fst, Function.update_self] using ha
    · simp only [productPoint, lift_snd]
      rw [← hb]
      apply (productPoint_eq_iff x R _ _ l).mpr
      intro β hβ
      have hne : β ≠ α := fun h => (List.nodup_cons.mp hl).1 (h ▸ hβ)
      exact Function.update_of_ne hne a b

private theorem productPoint_mul (x : ∀ α, RootCoordinate U α)
    (R : TestAlgebra k) (a : Root T → R) (l : List (Root T)) :
    productPoint x R a l ≫ rootProduct U l =
      (l.map (fun α => rootPoint ((x α).iso.hom ≫ (U α).val.inclusion) R (a α))).prod := by
  induction l with
  | nil => exact MonObj.comp_one _
  | cons α l ih =>
    simp only [productPoint, rootProduct, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
      List.map_cons, List.prod_cons, ih]
    rfl

private theorem cocharacterPoint_postcompose {G H : GroupScheme k} (c : Cocharacter H)
    (i : H ⟶ G) (R : TestAlgebra k) (t : Rˣ) :
    cocharacterPoint (c ≫ i) R t = cocharacterPoint c R t ≫ i.hom.hom := by
  unfold cocharacterPoint
  rw [Functor.map_comp, NatTrans.comp_app]
  rfl

private theorem rootPoint_orbit (x : ∀ α, RootCoordinate U α)
    (c : Cocharacter T.group) (R : TestAlgebra k) (t : Rˣ)
    (a : R) (α : Root T) :
    let g := cocharacterPoint (c ≫ T.inclusion) R t
    g * rootPoint ((x α).iso.hom ≫ (U α).val.inclusion) R a * g⁻¹ =
      rootPoint ((x α).iso.hom ≫ (U α).val.inclusion) R
        ((↑(t ^ pairing T.group α.val c) : R) * a) := by
  dsimp only
  rw [cocharacterPoint_postcompose,
    ← (CharacterPairing.characterPairingComposition T.group α.val c).2]
  exact (x α).scalar R (cocharacterPoint c R t) a

private def contractingProductPoint (x : ∀ α, RootCoordinate U α)
    (c : Cocharacter T.group) (R : TestAlgebra k) (a : Root T → R)
    (l : List (Root T)) : Points (ProductScheme U l) (polynomialAlgebra R) :=
  productPoint x (polynomialAlgebra R)
    (fun α => Polynomial.C (a α) * Polynomial.X ^ (pairing T.group α.val c).toNat) l

private theorem contractingProductPoint_zero (x : ∀ α, RootCoordinate U α)
    (c : Cocharacter T.group) (R : TestAlgebra k) (a : Root T → R)
    (l : List (Root T)) (hpos : ∀ α ∈ l, α ∈ positiveRoots T c) :
    mapPoints (polynomialEvaluate R 0) (contractingProductPoint x c R a l) =
      productPoint x R 0 l := by
  rw [contractingProductPoint, productPoint_map]
  apply (productPoint_eq_iff x R _ _ l).mpr
  intro α hα
  have h := hpos α hα
  change 0 < pairing T.group α.val c at h
  have hn : (pairing T.group α.val c).toNat ≠ 0 := by omega
  change Polynomial.aevalTower (AlgHom.id k R) (0 : R)
    (Polynomial.C (a α) * Polynomial.X ^ (pairing T.group α.val c).toNat) = 0
  simp [hn]

private theorem contractingProductPoint_one (x : ∀ α, RootCoordinate U α)
    (c : Cocharacter T.group) (R : TestAlgebra k) (a : Root T → R)
    (l : List (Root T)) :
    mapPoints (polynomialEvaluate R 1) (contractingProductPoint x c R a l) =
      productPoint x R a l := by
  rw [contractingProductPoint, productPoint_map]
  apply (productPoint_eq_iff x R _ _ l).mpr
  intro α _
  change Polynomial.aevalTower (AlgHom.id k R) (1 : R)
    (Polynomial.C (a α) * Polynomial.X ^ (pairing T.group α.val c).toNat) = a α
  simp

private theorem contractingProductPoint_restrict (x : ∀ α, RootCoordinate U α)
    (c : Cocharacter T.group) (R : TestAlgebra k) (a : Root T → R)
    (l : List (Root T)) (hpos : ∀ α ∈ l, α ∈ positiveRoots T c) :
    mapPoints (polynomialToLaurent R) (contractingProductPoint x c R a l ≫ rootProduct U l) =
      orbit (c ≫ T.inclusion) (productPoint x R a l ≫ rootProduct U l) := by
  change mapPoints (polynomialToLaurent R) (contractingProductPoint x c R a l) ≫
    rootProduct U l = _
  rw [contractingProductPoint, productPoint_map]
  unfold orbit
  rw [show mapPoints (laurentConstants R) (productPoint x R a l ≫ rootProduct U l) =
      mapPoints (laurentConstants R) (productPoint x R a l) ≫ rootProduct U l from rfl,
    productPoint_map, productPoint_mul, productPoint_mul]
  let g := cocharacterPoint (c ≫ T.inclusion) (laurentAlgebra R) (laurentParameter R)
  let f := (MulAut.conj g).toMonoidHom
  let w := l.map (fun α =>
    rootPoint ((x α).iso.hom ≫ (U α).val.inclusion) (laurentAlgebra R) ((laurentConstants R).hom (a α)))
  change _ = f w.prod
  rw [MonoidHom.map_list_prod]
  apply congrArg List.prod
  change _ = (l.map _).map f
  rw [List.map_map]
  apply List.map_congr_left
  intro α hα
  change _ = g * _ * g⁻¹
  rw [rootPoint_orbit]
  congr 1
  have h := hpos α hα
  change 0 < pairing T.group α.val c at h
  have hpow : laurentParameter R ^ pairing T.group α.val c =
      laurentParameter R ^ (pairing T.group α.val c).toNat := by
    rw [← zpow_natCast, Int.toNat_of_nonneg h.le]
  rw [hpow]
  change Polynomial.toLaurent (Polynomial.C (a α) * Polynomial.X ^ _) =
    (laurentParameter R).val ^ _ * LaurentPolynomial.C (a α)
  rw [map_mul, map_pow, Polynomial.toLaurent_C, Polynomial.toLaurent_X, mul_comm]
  rfl

end ProductPoints

open scoped TensorProduct Matrix DirectSum

open Specs.CharacterPairing (adjointWeightVectors adjointWeightSpace)
open Specs.CharacterDescent (Character StandardLattice)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap)
open Specs.AdjointRepresentation (dualMap constants scale conjugate)
open WeightDecomposition (weightSpace mem_weightSpace)
open RationalRepresentations

open private splitPresentation charactersOfIso characterValue_monomial algebraPoint
  adjointWeightVectors_iff extendCoordinates canonicalZero_eq
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private parameter_zpow
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent

/-- Identify the weight submodules of the split torus comodule with the
scheme-valued weight condition used to define absolute roots. -/
private theorem torusWeightComodule (G : AffineAlgebraicGroup k)
    (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group) (s : IdentityLieStructure G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∃ (r : ℕ) (χ : StandardLattice.{u} r ≃* Character T.group)
      (ρ : RightComodule k
        (groupAlgebra k (StandardLattice.{u} r)) (Specs.Lie k G.val)),
      ∀ (m : StandardLattice.{u} r) (v : Specs.Lie k G.val),
        v ∈ weightSpace ρ m ↔ v ∈ adjointWeightVectors T (χ m) := by
  classical
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation hT
  obtain ⟨χ, _, hχ, _, _⟩ := LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing (k := k) r
  obtain ⟨n, b, C, L, l, Ad, hAd, _, _⟩ := adjointRepresentation k G s
  let M := StandardLattice.{u} r
  let V := Specs.Lie k G.val
  let A := groupAlgebra k M
  let J := ULift.{u} (Fin n)
  let F : AffineGroupCategory k := ⟨(Specs.DiagonalizableGroups.diagonalGroup k M).val,
    (Specs.DiagonalizableGroups.diagonalGroup k M).property.1⟩
  let f := i.hom ≫ T.inclusion ≫ Ad
  let e := hopfSpecPointIso A
  obtain ⟨E, hE⟩ := representationCoactionComparison A b F L.val e l
  let ρ := E f
  let c := χ.trans (charactersOfIso i)
  refine ⟨r, c, ρ, ?_⟩
  intro m v
  rw [adjointWeightVectors_iff C l Ad hAd T (c m) v]
  let point (R : TestAlgebra k) (a : A →ₐ[k] R) : GroupPoints T.group R :=
    (e.hom.app R (WithConv.toConv a)) ≫ i.hom.hom.hom
  have hpoint (R : TestAlgebra k) : Function.Surjective (point R) := by
    intro t
    let a := (e.inv.app R (t ≫ i.inv.hom.hom)).ofConv
    refine ⟨a, ?_⟩
    have h := Iso.inv_hom_id_app e R
    change (e.hom.app R (e.inv.app R (t ≫ i.inv.hom.hom)) : GroupPoints F.val R) ≫
      i.hom.hom.hom = t
    rw [← GrpCat.comp_apply, h]
    let j := (underlying k).mapIso i
    change t ≫ j.inv ≫ j.hom = t
    rw [j.inv_hom_id]
    exact Category.comp_id (t : Points T.group.X R)
  have hchar (R : TestAlgebra k) (a : A →ₐ[k] R) :
      characterValue (c m) R (point R a) = a (MonoidAlgebra.of k M m) := by
    have heq : (point R a) ≫ (c m).hom.hom =
        (e.hom.app R (WithConv.toConv a) : GroupPoints F.val R) ≫ (χ m).hom.hom := by
      let j := (underlying k).mapIso i
      change (_ ≫ j.hom) ≫ j.inv ≫ (underlying k).map (χ m) = _
      rw [Category.assoc, j.hom_inv_id_assoc]
      rfl
    unfold characterValue
    dsimp only
    rw [heq]
    change characterValue (χ m) R (algebraPoint R a) = _
    rw [hχ, characterValue_monomial]
    rfl
  let ψ (R : TestAlgebra k) : V ⊗[k] R ≃ₗ[k] (J → R) :=
    (TensorProduct.comm k V R).trans ((b.baseChange R).equivFun.restrictScalars k)
  have hψ (R : TestAlgebra k) (w : V) (a : R) (j : J) :
      ψ R (w ⊗ₜ[k] a) j = algebraMap k R (b.equivFun w j) * a := by
    change (b.baseChange R).repr (a ⊗ₜ[k] w) j = _
    rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def]
    rfl
  have hev (R : TestAlgebra k) (a : A →ₐ[k] R) :
      let Q := (l.hom.app R).hom (((groupPointsFunctor k).map (T.inclusion ≫ Ad)).app R (point R a))
      ψ R (evaluate A ρ a v) = Q.val *ᵥ extendCoordinates b R v := by
    let Q := (l.hom.app R).hom (((groupPointsFunctor k).map f).app R (e.hom.app R (WithConv.toConv a)))
    have hQ : (l.hom.app R).hom
        (((groupPointsFunctor k).map (T.inclusion ≫ Ad)).app R (point R a)) = Q := by
      dsimp only [point, Q, f]
      rw [Functor.map_comp, NatTrans.comp_app]
      rfl
    dsimp only
    rw [hQ]
    change (ψ R).toLinearMap.comp (evaluate A ρ a) v =
      ((Matrix.mulVecLin Q.val).restrictScalars k).comp (extendCoordinates b R) v
    congr 1
    apply b.ext
    intro j
    change ψ R (evaluate A ρ a (b j)) = Q.val *ᵥ extendCoordinates b R (b j)
    rw [evaluationComparison A b F L.val e l f ρ (hE f) R a j]
    ext h
    change ψ R (∑ i, b i ⊗ₜ[k] Q.val i j) h =
      (Q.val *ᵥ (fun i => algebraMap k R (b.equivFun (b j) i))) h
    simp only [map_sum, Finset.sum_apply, hψ, Module.Basis.equivFun_self]
    simp [Matrix.mulVec, dotProduct, eq_comm]
  have weight (R : TestAlgebra k) (a : A →ₐ[k] R) :
      (let Q := (l.hom.app R).hom (((groupPointsFunctor k).map (T.inclusion ≫ Ad)).app R (point R a))
       Q.val *ᵥ extendCoordinates b R v = characterValue (c m) R (point R a) • extendCoordinates b R v) ↔
      evaluate A ρ a v = v ⊗ₜ[k] a (MonoidAlgebra.of k M m) := by
    dsimp only
    rw [← hev R a, hchar R a, ← (ψ R).injective.eq_iff]
    have hmul : ψ R (v ⊗ₜ[k] a (MonoidAlgebra.of k M m)) =
        a (MonoidAlgebra.of k M m) • extendCoordinates b R v := by
      funext j
      rw [hψ]
      exact mul_comm _ _
    rw [hmul]
  constructor
  · intro hv R t
    obtain ⟨a, rfl⟩ := hpoint R t
    apply (weight R a).mpr
    rw [evaluate, LinearMap.comp_apply, mem_weightSpace.mp hv, LinearMap.lTensor_tmul]
    rfl
  · intro hv
    apply mem_weightSpace.mpr
    have h := (weight (CommAlgCat.of k A) (AlgHom.id k A)).mp (hv _ _)
    simpa only [evaluate, LinearMap.comp_apply, AlgHom.toLinearMap_id, LinearMap.lTensor_id, LinearMap.id_apply,
      AlgHom.id_apply] using h

private theorem cocharacter_weight_support (G : AffineAlgebraicGroup k)
    (T : ClosedSubgroup G.val) (c : Cocharacter T.group) (s : IdentityLieStructure G.val)
    (W : AdjointWeightBasis (c ≫ T.inclusion) s) (χ : Character T.group)
    (v : Specs.Lie k G.val) (hv : v ∈ adjointWeightVectors T χ) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ j, W.weight j ≠ pairing T.group χ c → W.basis.equivFun v j = 0 := by
  letI := s.lieRing
  letI := s.lieAlgebra
  let R := CommAlgCat.of k k
  let S := laurentAlgebra R
  let t := laurentParameter R
  let a : R ⟶ S := CommAlgCat.ofHom (Algebra.ofId k S)
  let w := fun j => a.hom (W.basis.equivFun v j)
  have hn : (W.coordinates.equiv S w).toMul.val = mapPoints (dualMap a) v.toMul.val :=
    (W.coordinates.naturality a _).trans
      (congrArg (mapPoints (dualMap a)) (W.coordinates.at_base v))
  have h := hv S (cocharacterPoint c S t)
  change mapPoints (constants S) (cocharacterPoint c S t ≫ T.inclusion.hom.hom) *
      mapPoints (dualMap a) v.toMul.val *
        (mapPoints (constants S) (cocharacterPoint c S t ≫ T.inclusion.hom.hom))⁻¹ =
    mapPoints (scale S (characterValue χ S (cocharacterPoint c S t)))
      (mapPoints (dualMap a) v.toMul.val) at h
  rw [← hn] at h
  change conjugate (cocharacterPoint c S t ≫ T.inclusion.hom.hom)
      (W.coordinates.equiv S w) =
    mapPoints (scale S (characterValue χ S (cocharacterPoint c S t)))
      (W.coordinates.equiv S w).toMul.val at h
  rw [← cocharacterPoint_postcompose, ← W.diagonal, ← W.coordinates.smul,
    (CharacterPairing.characterPairingComposition T.group χ c).2] at h
  have he := (W.coordinates.equiv S).injective (Subtype.ext h)
  intro j hj
  have he' := congrFun he j
  change (↑(t ^ W.weight j) : S) * w j =
    (↑(t ^ pairing T.group χ c) : S) * w j at he'
  rw [parameter_zpow, parameter_zpow] at he'
  change LaurentPolynomial.T (W.weight j) * LaurentPolynomial.C (W.basis.equivFun v j) =
    LaurentPolynomial.T (pairing T.group χ c) * LaurentPolynomial.C (W.basis.equivFun v j) at he'
  rw [mul_comm (LaurentPolynomial.T (W.weight j)), mul_comm (LaurentPolynomial.T (pairing T.group χ c)),
    ← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T] at he'
  have he'' := congrArg (fun p : LaurentPolynomial k => p.coeff (W.weight j)) he'
  change (AddMonoidAlgebra.single (W.weight j) (W.basis.equivFun v j) :
      LaurentPolynomial k).coeff (W.weight j) =
    (AddMonoidAlgebra.single (pairing T.group χ c) (W.basis.equivFun v j) :
      LaurentPolynomial k).coeff (W.weight j) at he''
  simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
    ite_eq_left rfl, ite_true, ite_eq_right (Ne.symm hj)] using he''

open private characterValue_one from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private weightProjection projection_of_mem
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.WeightDecomposition

private theorem pairing_trivial (T : GroupScheme k) (c : Cocharacter T) :
    pairing T (1 : Character T) c = 0 := by
  let R := CommAlgCat.of k k
  have h := (CharacterPairing.characterPairingComposition T 1 c).2
    (laurentAlgebra R) (laurentParameter R)
  rw [characterValue_one, parameter_zpow] at h
  change (1 : LaurentPolynomial k) = LaurentPolynomial.T (pairing T 1 c) at h
  by_contra hn
  have he : (LaurentPolynomial.T 0 : LaurentPolynomial k) =
      LaurentPolynomial.T (pairing T 1 c) :=
    LaurentPolynomial.T_zero.trans h
  change (AddMonoidAlgebra.single 0 1 : LaurentPolynomial k) =
    AddMonoidAlgebra.single (pairing T 1 c) 1 at he
  have hc := congrArg (fun p : LaurentPolynomial k => p.coeff 0) he
  have hzero : (1 : k) = 0 := by
    simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      ite_eq_left rfl, ite_true, ite_eq_right hn] using hc
  exact one_ne_zero hzero

private theorem torusWeightBasis (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val)
    (hT : IsSplitTorus T.group) (s : IdentityLieStructure G.val) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∃ (I : Type u) (hI : Fintype I),
      letI := hI
      ∃ (b : Module.Basis I k (Specs.Lie k G.val)) (χ : I → Character T.group),
      (∀ j, b j ∈ adjointWeightVectors T (χ j)) ∧
      ∀ (α : Character T.group) (v : Specs.Lie k G.val), v ∈ adjointWeightVectors T α →
        ∀ j, χ j ≠ α → b.equivFun v j = 0 := by
  classical
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨r, c, ρ, hρ⟩ := torusWeightComodule G T hT s
  haveI : Module.Finite k (Specs.Lie k G.val) := by
    obtain ⟨_, b, _, _, _, _, _, _, _⟩ := adjointRepresentation k G s
    exact Module.Finite.of_basis b
  obtain ⟨I, hI, b, w, hw⟩ := DiagonalizableFixedLocus.existsWeightBasis ρ
  letI := Fintype.ofFinite I
  refine ⟨I, inferInstance, b, c ∘ w, fun j => (hρ _ _).mp (hw j), ?_⟩
  intro α v hv j hj
  let m := c.symm α
  have hm : α = c m := (c.apply_symm_apply α).symm
  have hvm : v ∈ weightSpace ρ m := (hρ _ _).mpr (hm ▸ hv)
  have hc : b.equivFun (weightProjection ρ m v) j = b.equivFun v j := by
    rw [projection_of_mem hvm, ite_eq_left rfl]
  suffices b.equivFun (weightProjection ρ m v) j = 0 by exact hc.symm.trans this
  have hne : w j ≠ m := fun h => hj (by change c (w j) = α; rw [h, ← hm])
  let L := (LinearMap.proj j).comp (b.equivFun.toLinearMap.comp (weightProjection ρ m))
  have hL : L = 0 := by
    apply b.ext
    intro i
    change b.equivFun (weightProjection ρ m (b i)) j = 0
    rw [projection_of_mem (hw i)]
    split
    · rename_i hi
      have hij : i ≠ j := fun h => hne (h ▸ hi)
      simp [Module.Basis.equivFun_self, hij]
    · simp
  exact DFunLike.congr_fun hL v

/-- Changing bases preserves the positive span when each vector of the
second basis belongs to the indicated weight space of the first. -/
private theorem positive_basis_support {V I J : Type u} [AddCommGroup V]
    [Module k V] [Fintype I] [Fintype J] (b : Module.Basis I k V)
    (d : Module.Basis J k V) (p : I → ℤ) (q : J → ℤ)
    (h : ∀ i j, q j ≠ p i → d.equivFun (b i) j = 0) (v : V) :
    (∀ j, q j ≤ 0 → d.equivFun v j = 0) ↔ (∀ i, p i ≤ 0 → b.equivFun v i = 0) := by
  classical
  let vpos := ∑ i ∈ Finset.univ.filter (fun i => 0 < p i), b.equivFun v i • b i
  let vnonpos := ∑ i ∈ Finset.univ.filter (fun i => p i ≤ 0), b.equivFun v i • b i
  have hsplit : vpos + vnonpos = v := by
    rw [show vnonpos = ∑ i ∈ Finset.univ.filter (fun i => ¬ 0 < p i),
      b.equivFun v i • b i from by simp only [not_lt, vnonpos]]
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => 0 < p i) _).trans
      (b.sum_equivFun v)
  have hpos j (hj : q j ≤ 0) : d.equivFun vpos j = 0 := by
    simp only [vpos, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_eq_zero
    intro i hi
    rw [h i j (by have hi' := (Finset.mem_filter.mp hi).2; omega), smul_zero]
  have hnonpos j (hj : 0 < q j) : d.equivFun vnonpos j = 0 := by
    simp only [vnonpos, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_eq_zero
    intro i hi
    rw [h i j (by have hi' := (Finset.mem_filter.mp hi).2; omega), smul_zero]
  constructor
  · intro hv
    have hz : vnonpos = 0 := by
      apply d.equivFun.injective
      rw [map_zero]
      funext j
      change d.equivFun vnonpos j = 0
      by_cases hj : 0 < q j
      · exact hnonpos j hj
      · have hj' := not_lt.mp hj
        have he := congrArg (fun x => d.equivFun x j) hsplit
        simpa only [map_add, Pi.add_apply, hpos j hj', hv j hj', zero_add] using he
    intro i hi
    have he : b.equivFun vnonpos i = b.equivFun v i := by
      simp only [vnonpos, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)]
      · simp [Module.Basis.equivFun_self]
      · intro j _ hne
        have hbji : b.equivFun (b j) i = 0 := by
          rw [Module.Basis.equivFun_self]
          simp [hne]
        rw [hbji, smul_zero]
    simpa only [hz, map_zero, Pi.zero_apply] using he.symm
  · intro hv
    have hz : vnonpos = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hv i (Finset.mem_filter.mp hi).2, zero_smul]
    rw [hz, add_zero] at hsplit
    rw [← hsplit]
    exact hpos

private theorem contracting_tangent_support (G : AffineAlgebraicGroup k)
    (T : ClosedSubgroup G.val) (c : Cocharacter T.group)
    (D : LimitDecomposition (c ≫ T.inclusion)) (s : IdentityLieStructure G.val)
    {I : Type u} [Fintype I] (b : letI := s.lieRing; letI := s.lieAlgebra;
      Module.Basis I k (Specs.Lie k G.val)) (χ : I → Character T.group)
    (hb : ∀ j, b j ∈ adjointWeightVectors T (χ j)) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ v : Specs.Lie k G.val, v ∈ lieImage D.contracting ↔
      ∀ j, pairing T.group (χ j) c ≤ 0 → b.equivFun v j = 0 := by
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨W, _, hW, _⟩ := lieWeights G (c ≫ T.inclusion) D s
  intro v
  rw [hW]
  exact positive_basis_support b W.basis (fun j => pairing T.group (χ j) c)
    W.weight (fun i => cocharacter_weight_support G T c s W _ _ (hb i)) v

section ProductTangent

variable {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val} {U : RootSubgroupFamily T}

private abbrev baseAlgebra (k : Type u) [Field k] := CommAlgCat.of k k
private abbrev dualAlgebra (k : Type u) [Field k] := CommAlgCat.of k (DualNumber k)

/-- Tangent lifts at a specified rational point, expressed on dual numbers. -/
private abbrev TangentLifts {X : SchemeOver k} (q : Points X (baseAlgebra k)) :=
  {p : Points X (dualAlgebra k) // mapPoints (dualReduction k) p = q}

private def tangentMap {X Y : SchemeOver k} (f : X ⟶ Y) {q : Points X (baseAlgebra k)} :
    TangentLifts q → TangentLifts (q ≫ f) :=
  fun p => ⟨p.val ≫ f, congrArg (· ≫ f) p.property⟩

private def rootTangent (x : ∀ α, RootCoordinate U α) (a : Root T → k) (α : Root T) :
    Specs.Lie k (U α).val.group := by
  let p := rootPoint (x α).iso.hom (dualAlgebra k) (TrivSqZeroExt.inr (a α))
  refine ⟨p, ?_⟩
  change mapPoints (dualReduction k) p = 1
  rw [rootPoint_map]
  exact rootPoint_zero _ _

private theorem rootTangent_surjective (x : ∀ α, RootCoordinate U α) (α : Root T)
    (p : Specs.Lie k (U α).val.group) :
    ∃ a : k, rootTangent x (fun _ => a) α = p := by
  obtain ⟨a, ha⟩ := rootPoint_surjective (x α).iso (dualAlgebra k) p.toMul.val
  have h := p.toMul.property
  change mapPoints (dualReduction k) p.toMul.val = 1 at h
  rw [← ha, rootPoint_map, ← rootPoint_zero (x α).iso.hom] at h
  have hz := rootPoint_injective (x α).iso (baseAlgebra k) h
  change a.fst = 0 at hz
  refine ⟨a.snd, Subtype.ext ?_⟩
  change rootPoint (x α).iso.hom (dualAlgebra k) (TrivSqZeroExt.inr a.snd) = p.toMul.val
  rw [show (TrivSqZeroExt.inr a.snd : DualNumber k) = a from TrivSqZeroExt.ext hz.symm rfl]
  exact ha

private def productTangent (x : ∀ α, RootCoordinate U α) (a : Root T → k)
    (l : List (Root T)) : TangentLifts (productPoint x (baseAlgebra k) 0 l) :=
  ⟨productPoint x (dualAlgebra k) (fun α => TrivSqZeroExt.inr (a α)) l, by
    rw [productPoint_map]
    rfl⟩

private theorem productTangent_surjective (x : ∀ α, RootCoordinate U α)
    (l : List (Root T)) (hl : l.Nodup) : Function.Surjective (productTangent x · l) := by
  intro p
  obtain ⟨a, ha⟩ := productPoint_surjective x (dualAlgebra k) l hl p.val
  have hp := p.property
  rw [← ha, productPoint_map] at hp
  have hzero := (productPoint_eq_iff x (baseAlgebra k) _ _ l).mp hp
  refine ⟨fun α => (a α).snd, Subtype.ext ?_⟩
  rw [← ha]
  apply (productPoint_eq_iff x (dualAlgebra k) _ _ l).mpr
  intro α hα
  exact TrivSqZeroExt.ext (hzero α hα).symm rfl

private theorem productPoint_base (x : ∀ α, RootCoordinate U α) (l : List (Root T))
    {H : GroupScheme k} (p : ProductScheme U l ⟶ H.X) (j : H ⟶ G.val)
    (hj : Mono j.hom.hom) (hp : p ≫ j.hom.hom = rootProduct U l) :
    productPoint x (baseAlgebra k) 0 l ≫ p = 1 := by
  apply (cancel_mono j.hom.hom).mp
  rw [Category.assoc, hp, productPoint_mul, MonObj.one_comp]
  induction l with
  | nil => rfl
  | cons α l ih => simp [rootPoint_zero]

private theorem rootTangent_list_sum (s : IdentityLieStructure G.val)
    (x : ∀ α, RootCoordinate U α) (a : Root T → k) (l : List (Root T)) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ((l.map (fun α => mapPointKernel (U α).val.inclusion (rootTangent x a α))).sum).toMul.val =
      (productTangent x a l).val ≫ rootProduct U l := by
  letI := s.lieRing
  letI := s.lieAlgebra
  rw [show (productTangent x a l).val =
    productPoint x (dualAlgebra k) (fun α => TrivSqZeroExt.inr (a α)) l from rfl,
    productPoint_mul]
  induction l with
  | nil =>
    rfl
  | cons α l ih =>
    simp only [List.map_cons, List.sum_cons, List.prod_cons]
    have hadd (p q : Specs.Lie k G.val) : (p + q).toMul.val = p.toMul.val * q.toMul.val := rfl
    rw [hadd, ih]
    rfl

private theorem basis_index_for_root (hRoots : RootSubgroups.{u}) (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group)
    (hmax : IsGeometricallyMaximal T) (s : IdentityLieStructure G.val)
    {I : Type u} [Fintype I] (b : letI := s.lieRing; letI := s.lieAlgebra;
      Module.Basis I k (Specs.Lie k G.val)) (χ : I → Character T.group)
    (hb : ∀ j, b j ∈ adjointWeightVectors T (χ j))
    (hs : ∀ α v, v ∈ adjointWeightVectors T α → ∀ j, χ j ≠ α → (by
      letI := s.lieRing
      letI := s.lieAlgebra
      exact b.equivFun v j = 0)) (α : Root T) : ∃! j, χ j = α.val := by
  classical
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨_, v, hv, hne⟩ := α.property
  have h₁ : ∃ j, χ j = α.val := by
    by_contra h
    apply hne
    rw [canonicalZero_eq s]
    apply b.equivFun.injective
    exact (funext fun j => hs _ _ hv j (fun hj => h ⟨j, hj⟩)).trans b.equivFun.map_zero.symm
  obtain ⟨i, hi⟩ := h₁
  refine ⟨i, hi, fun j hj => ?_⟩
  let W := adjointWeightSpace T α.val s
  let v₀ : W := ⟨b i, Submodule.subset_span (hi ▸ hb i)⟩
  let v₁ : W := ⟨b j, Submodule.subset_span (hj ▸ hb j)⟩
  have hne₀ : v₀ ≠ 0 := fun h => b.ne_zero i (congrArg Subtype.val h)
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' v₀ hne₀).mp
    (((hRoots G hG T hT hmax).2 α.val α.property).1 s) v₁
  by_contra hij
  have he := congrArg (fun x : W => b.equivFun (x : Specs.Lie k G.val) j) ha
  simp only [Submodule.coe_smul, v₀, v₁] at he
  simp [Module.Basis.equivFun_self, hij] at he

/-- The differential of the order-sensitive group product is the order-independent
sum of the distinct positive weight lines. -/
private theorem product_tangent_bijective (hRoots : RootSubgroups.{u}) (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group)
    (hmax : IsGeometricallyMaximal T) (U : RootSubgroupFamily T)
    (x : ∀ α, RootCoordinate U α) (c : Cocharacter T.group)
    (D : LimitDecomposition (c ≫ T.inclusion)) (l : List (Root T))
    (hl : Enumerates l (positiveRoots T c)) (p : ProductScheme U l ⟶ D.contracting.group.X)
    (hp : p ≫ D.contracting.inclusion.hom.hom = rootProduct U l) :
    Function.Bijective (tangentMap p (q := productPoint x (baseAlgebra k) 0 l)) := by
  classical
  letI := D.contracting.isClosedImmersion
  letI : Mono D.contracting.inclusion.hom.hom := Over.mono_of_mono_left _
  let s := identityLieStructure G
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨I, hI, b, χ, hb, hs⟩ := torusWeightBasis G T hT s
  letI := hI
  have support := contracting_tangent_support G T c D s b χ hb
  have unique (α : Root T) := basis_index_for_root hRoots G hG T hT hmax s b χ hb hs α
  let idx (α : Root T) := Classical.choose (unique α)
  have hidx (α : Root T) : χ (idx α) = α.val := (Classical.choose_spec (unique α)).1
  have uniq (α : Root T) (i : I) (hi : χ i = α.val) : i = idx α :=
    (Classical.choose_spec (unique α)).2 i hi
  let v (a : Root T → k) (α : Root T) : Specs.Lie k G.val :=
    mapPointKernel (U α).val.inclusion (rootTangent x a α)
  let total (a : Root T → k) : Specs.Lie k G.val := (l.map (v a)).sum
  have hv (a : Root T → k) (α : Root T) : v a α ∈ adjointWeightVectors T α.val := by
    rw [← (x α).tangentRange]
    exact Set.mem_range_self _
  have hi (a : Root T → k) (i : I) (α : Root T) (ha : χ i ≠ α.val) :
      b.equivFun (v a α) i = 0 := hs _ _ (hv a α) i ha
  have htotal (a : Root T → k) :
      (tangentMap p (productTangent x a l)).val ≫ D.contracting.inclusion.hom.hom =
        (total a).toMul.val := by
    change ((productTangent x a l).val ≫ p) ≫ D.contracting.inclusion.hom.hom = _
    rw [Category.assoc, hp, ← rootTangent_list_sum s]
  have hsum (a : Root T → k) (i : I) :
      b.equivFun (total a) i = ∑ α ∈ l.toFinset, b.equivFun (v a α) i := by
    let f := (LinearMap.proj i).comp b.equivFun.toLinearMap
    change f ((l.map (v a)).sum) = _
    rw [map_list_sum, List.map_map]
    symm
    exact List.sum_toFinset _ hl.1
  have hsum_at (a : Root T → k) (α : Root T) (ha : α ∈ l) :
      b.equivFun (total a) (idx α) = b.equivFun (v a α) (idx α) := by
    rw [hsum]
    apply Finset.sum_eq_single_of_mem α (List.mem_toFinset.mpr ha)
    intro β hβ hne
    apply hi a _ β
    intro h
    exact hne (Subtype.ext (h.symm.trans (hidx α)))
  constructor
  · intro q r h
    obtain ⟨a, rfl⟩ := productTangent_surjective x l hl.1 q
    obtain ⟨a', rfl⟩ := productTangent_surjective x l hl.1 r
    have he : total a = total a' := by
      apply Subtype.ext
      change (total a).toMul.val = (total a').toMul.val
      exact (htotal a).symm.trans ((congrArg (·.val ≫ D.contracting.inclusion.hom.hom) h).trans
        (htotal a'))
    apply Subtype.ext
    apply (productPoint_eq_iff x (dualAlgebra k) _ _ l).mpr
    intro α ha
    have heq : v a α = v a' α := by
      apply b.equivFun.injective
      funext i
      by_cases hχ : χ i = α.val
      · rw [uniq α i hχ, ← hsum_at a α ha, ← hsum_at a' α ha, he]
      · rw [hi a i α hχ, hi a' i α hχ]
    apply rootPoint_injective (x α).iso (dualAlgebra k)
    letI := (U α).val.isClosedImmersion
    letI : Mono (U α).val.inclusion.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono (U α).val.inclusion.hom.hom).mp
    exact congrArg (fun q : Specs.Lie k G.val => q.toMul.val) heq
  · intro q
    have hbase := productPoint_base x l p D.contracting.inclusion inferInstance hp
    let q' : Specs.Lie k D.contracting.group := ⟨q.val, q.property.trans hbase⟩
    let w := mapPointKernel D.contracting.inclusion q'
    have hw := support w |>.mp (Set.mem_range_self q')
    have hchoose (α : Root T) :
        ∃ a : k, v (fun _ => a) α = b.equivFun w (idx α) • b (idx α) := by
      let t := b.equivFun w (idx α) • b (idx α)
      have ht : t ∈ adjointWeightVectors T α.val := by
        rw [← CharacterPairing.adjointWeightSpaceVectors G T s]
        exact (adjointWeightSpace T α.val s).smul_mem _
          (Submodule.subset_span (hidx α ▸ hb (idx α)))
      have ht' : t ∈ Set.range (mapPointKernel (U α).val.inclusion) := by
        rw [(x α).tangentRange]
        exact ht
      obtain ⟨z, hz⟩ := ht' 
      obtain ⟨a, ha⟩ := rootTangent_surjective x α z
      exact ⟨a, by dsimp only [v]; rw [ha]; exact hz⟩
    let a α := Classical.choose (hchoose α)
    have ha (α : Root T) : v a α = b.equivFun w (idx α) • b (idx α) :=
      Classical.choose_spec (hchoose α)
    refine ⟨productTangent x a l, Subtype.ext ((cancel_mono D.contracting.inclusion.hom.hom).mp ?_)⟩
    rw [htotal]
    change (total a).toMul.val = w.toMul.val
    apply congrArg (fun z : Specs.Lie k G.val => z.toMul.val)
    apply b.equivFun.injective
    funext i
    by_cases hi₀ : 0 < pairing T.group (χ i) c
    · have hroot : χ i ∈ absoluteRoots T := by
        refine ⟨fun h => ?_, b i, hb i, fun h => b.ne_zero i (h.trans (canonicalZero_eq s))⟩
        rw [h, pairing_trivial] at hi₀
        exact (lt_irrefl _ hi₀)
      let α : Root T := ⟨χ i, hroot⟩
      have hα : α ∈ l := (hl.2 α).mpr hi₀
      have he := uniq α i rfl
      rw [he, hsum_at a α hα, ha α]
      simp
    · rw [hw i (not_lt.mp hi₀), hsum]
      apply Finset.sum_eq_zero
      intro α hα
      apply hi a i α
      intro h
      apply hi₀
      rw [h]
      exact (hl.2 α).mp (List.mem_toFinset.mp hα)

end ProductTangent

open _root_.Specs.AdvCommAlg.Differentials.Tangent (PointLifts)

open private ext_lift from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent

section Cotangent

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

private def pullbackLifts (f : A →ₐ[k] B) (e : B →ₐ[k] k) :
    PointLifts k B k e → PointLifts k A k (e.comp f) :=
  fun p => ⟨p.val.comp f, by rw [← AlgHom.comp_assoc, p.property]⟩

private theorem cotangent_bijective_of_lifts (f : A →ₐ[k] B) (e : B →ₐ[k] k)
    (h : Function.Bijective (pullbackLifts f e)) :
    Function.Bijective (Ideal.mapCotangent (augmentationIdeal (e.comp f))
      (augmentationIdeal e) f (by intro a ha; exact ha)) := by
  obtain ⟨tA, hA, _⟩ := pointTangentLifts k A (e.comp f)
  obtain ⟨tB, hB, _⟩ := pointTangentLifts k B e
  let q := Ideal.mapCotangent (augmentationIdeal (e.comp f)) (augmentationIdeal e) f
    (by intro a ha; exact ha)
  apply LinearMap.dualMap_bijective_iff.mp
  change Function.Bijective q.dualMap
  have heq (L : PointTangent e) : pullbackLifts f e (tB L) = tA (q.dualMap L) := by
    apply ext_lift
    intro a
    change ((tB L).val (f a.val)).snd = ((tA (q.dualMap L)).val a).snd
    rw [hA]
    exact hB L ⟨f a.val, a.property⟩
  have hh := tA.symm.bijective.comp (h.comp tB.bijective)
  convert hh using 1
  funext L
  change _ = tA.symm (pullbackLifts f e (tB L))
  rw [heq, Equiv.symm_apply_apply]

end Cotangent

open private affinePointEquiv_natural polynomialContract polynomialContract_eq
  polynomialContract_natural polynomialContract_zero polynomialContract_one
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent

private abbrev affineSpec (A : TestAlgebra k) := (testSpec k).obj (op A)

private theorem affinePointEquiv_postcomp {X Y : SchemeOver k} {A B : TestAlgebra k}
    (eX : affineSpec B ≅ X) (eY : affineSpec A ≅ Y) (p : X ⟶ Y)
    (f : A →ₐ[k] B) (hf : (testSpec k).map (CommAlgCat.ofHom f).op ≫ eY.hom = eX.hom ≫ p)
    {R : TestAlgebra k} (x : B →ₐ[k] R) :
    affinePointEquiv eX R x ≫ p = affinePointEquiv eY R (x.comp f) := by
  change ((testSpec k).map (CommAlgCat.ofHom x).op ≫ eX.hom) ≫ p =
    (testSpec k).map ((CommAlgCat.ofHom f) ≫ (CommAlgCat.ofHom x)).op ≫ eY.hom
  rw [op_comp, Functor.map_comp, Category.assoc, Category.assoc, hf]

private theorem affinePointEquiv_polynomialEval {A R : TestAlgebra k} {X : SchemeOver k}
    (e : affineSpec A ≅ X) (p : Points X (polynomialAlgebra R)) (r : R) (a : A) :
    (((affinePointEquiv e (polynomialAlgebra R)).symm p) a).eval r =
      ((affinePointEquiv e R).symm (mapPoints (polynomialEvaluate R r) p)) a := by
  have h := affinePointEquiv_natural e (polynomialEvaluate R r)
    ((affinePointEquiv e (polynomialAlgebra R)).symm p)
  rw [Equiv.apply_symm_apply] at h
  have h' := congrArg (affinePointEquiv e R).symm h
  rw [Equiv.symm_apply_apply] at h'
  exact DFunLike.congr_fun h' a

private def affinePointEquiv_lifts {A : TestAlgebra k} {X : SchemeOver k}
    (e : affineSpec A ≅ X) {q : Points X (baseAlgebra k)} {ε : A →ₐ[k] k}
    (hε : affinePointEquiv e _ ε = q) :
    PointLifts k A k ε ≃ TangentLifts q := by
  refine (affinePointEquiv e (dualAlgebra k)).subtypeEquiv ?_
  intro z
  change (TrivSqZeroExt.fstHom k k k).comp z = ε ↔
      mapPoints (dualReduction k) (affinePointEquiv e _ z) = q
  rw [← hε, ← affinePointEquiv_natural e (dualReduction k),
    (affinePointEquiv e _).injective.eq_iff]
  rfl

section ContractingProduct

variable {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val} {U : RootSubgroupFamily T}

private theorem product_affine (l : List (Root T)) : IsAffine (ProductScheme U l).left := by
  induction l with
  | nil => exact inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
  | cons α l h =>
    letI := affine_subgroup G.property.1 (U α).val
    letI := h
    change IsAffine (Limits.pullback (U α).val.group.X.hom (ProductScheme U l).hom)
    infer_instance

private theorem contracting_product_isIso (hRoots : RootSubgroups.{u})
    (hG : IsReductive G) (hT : IsSplitTorus T.group) (hmax : IsGeometricallyMaximal T)
    (x : ∀ α, RootCoordinate U α) (c : Cocharacter T.group)
    (D : LimitDecomposition (c ≫ T.inclusion)) (l : List (Root T))
    (hl : Enumerates l (positiveRoots T c)) (p : ProductScheme U l ⟶ D.contracting.group.X)
    (hp : p ≫ D.contracting.inclusion.hom.hom = rootProduct U l) :
    IsIso p := by
  letI := D.contracting.isClosedImmersion
  letI : Mono D.contracting.inclusion.hom.hom := Over.mono_of_mono_left _
  obtain ⟨Aop, ⟨eY⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr
    (affine_subgroup G.property.1 D.contracting)
  obtain ⟨Bop, ⟨eX⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr (product_affine (U := U) l)
  let A := Aop.unop
  let B := Bop.unop
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let m := (F.preimage (eX.hom ≫ p ≫ eY.inv)).unop
  let f := m.hom
  have hm : (testSpec k).map m.op ≫ eY.hom = eX.hom ≫ p := by
    change (testSpec k).map (F.preimage (eX.hom ≫ p ≫ eY.inv)) ≫ eY.hom = _
    rw [F.map_preimage]
    simp
  have hcomp {R : TestAlgebra k} (z : B →ₐ[k] R) :
      affinePointEquiv eX R z ≫ p = affinePointEquiv eY R (z.comp f) :=
    affinePointEquiv_postcomp eX eY p f hm z
  let q := productPoint x (baseAlgebra k) 0 l
  let eB := (affinePointEquiv eX (baseAlgebra k)).symm q
  let eA := eB.comp f
  have hB : affinePointEquiv eX (baseAlgebra k) eB = q := (affinePointEquiv eX _).apply_symm_apply q
  have hA : affinePointEquiv eY (baseAlgebra k) eA = q ≫ p := (hcomp eB).symm.trans (by rw [hB])
  have hq : q ≫ p = 1 := productPoint_base x l p D.contracting.inclusion inferInstance hp
  have ht := product_tangent_bijective hRoots G hG T hT hmax U x c D l hl p hp
  let u := affinePointEquiv_lifts eX hB
  let v := affinePointEquiv_lifts eY hA
  have hlift : Function.Bijective (pullbackLifts f eB) := by
    have h := v.symm.bijective.comp (ht.comp u.bijective)
    convert h using 1
    funext z
    apply v.injective
    rw [Function.comp_apply, Equiv.apply_symm_apply]
    apply Subtype.ext
    exact (hcomp (R := dualAlgebra k) z.val).symm
  have hcot := cotangent_bijective_of_lifts f eB hlift
  let a₀ := affinePointEquiv eY A (AlgHom.id k A)
  let b₀ := affinePointEquiv eX B (AlgHom.id k B)
  obtain ⟨b, hb⟩ := productPoint_surjective x B l hl.1 b₀
  change productPoint x B b l = b₀ at hb
  let δA := (affinePointEquiv eY (polynomialAlgebra A)).symm
    (polynomialContract G.property.1 (c ≫ T.inclusion) D a₀)
  let δB := (affinePointEquiv eX (polynomialAlgebra B)).symm (contractingProductPoint x c B b l)
  have hpos : ∀ α ∈ l, α ∈ positiveRoots T c := fun α hα => (hl.2 α).mp hα
  have hcompat : δB.comp f = (mapPolynomial m).hom.comp δA := by
    apply (affinePointEquiv eY (polynomialAlgebra B)).injective
    rw [← hcomp, affinePointEquiv_natural eY (mapPolynomial m)]
    dsimp only [δA, δB]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← polynomialContract_natural]
    symm
    apply polynomialContract_eq
    change mapPoints (polynomialToLaurent B)
        ((contractingProductPoint x c B b l ≫ p) ≫ D.contracting.inclusion.hom.hom) =
      orbit (c ≫ T.inclusion) (mapPoints m a₀ ≫ D.contracting.inclusion.hom.hom)
    rw [Category.assoc, hp, contractingProductPoint_restrict x c B b l hpos]
    congr 1
    rw [hb, ← hp, ← Category.assoc]
    have h := affinePointEquiv_natural eY m (AlgHom.id k A)
    rw [show m.hom.comp (AlgHom.id k A) = (AlgHom.id k B).comp f from rfl] at h
    exact congrArg (· ≫ D.contracting.inclusion.hom.hom) ((hcomp _).trans h)
  have hδ (a : A) (n : ℕ) : (δB (f a)).coeff n = f ((δA a).coeff n) := by
    have h := congrArg (fun z : A →ₐ[k] Polynomial B => (z a).coeff n) hcompat
    exact h.trans (Polynomial.coeff_map f.toRingHom n)
  have eA₀ (a : A) : (δA a).coeff 0 = algebraMap k A (eA a) := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    change (_ : Polynomial A).eval 0 = _
    rw [affinePointEquiv_polynomialEval, polynomialContract_zero]
    have h := affinePointEquiv_natural eY (CommAlgCat.ofHom (Algebra.ofId k A)) eA
    rw [hA, hq] at h
    change affinePointEquiv eY A ((Algebra.ofId k A).comp eA) = _ at h
    rw [show (mapPoints (CommAlgCat.ofHom (Algebra.ofId k A))
      (1 : GroupPoints D.contracting.group (baseAlgebra k)) : GroupPoints D.contracting.group A) = 1
      from map_one (((groupPointsFunctor k).obj _).map _).hom] at h
    exact DFunLike.congr_fun ((affinePointEquiv eY A).symm_apply_eq.mpr h.symm) a
  have eA₁ (a : A) : (δA a).eval 1 = a := by
    change (_ : Polynomial A).eval 1 = _
    rw [affinePointEquiv_polynomialEval, polynomialContract_one]
    exact DFunLike.congr_fun ((affinePointEquiv eY A).symm_apply_apply (AlgHom.id k A)) a
  have eB₀ (b' : B) : (δB b').coeff 0 = algebraMap k B (eB b') := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    change (_ : Polynomial B).eval 0 = _
    rw [affinePointEquiv_polynomialEval, contractingProductPoint_zero x c B b l hpos]
    have h := affinePointEquiv_natural eX (CommAlgCat.ofHom (Algebra.ofId k B)) eB
    rw [hB, productPoint_map] at h
    have eq : productPoint x B (fun α => (Algebra.ofId k B) ((0 : Root T → k) α)) l =
        productPoint x B 0 l := by
      apply (productPoint_eq_iff x B _ _ l).mpr
      intro α _
      exact map_zero (Algebra.ofId k B)
    change affinePointEquiv eX B ((Algebra.ofId k B).comp eB) =
      productPoint x B (fun α => (Algebra.ofId k B) ((0 : Root T → k) α)) l at h
    rw [eq] at h
    exact DFunLike.congr_fun ((affinePointEquiv eX B).symm_apply_eq.mpr h.symm) b'
  have eB₁ (b' : B) : (δB b').eval 1 = b' := by
    change (_ : Polynomial B).eval 1 = _
    rw [affinePointEquiv_polynomialEval, contractingProductPoint_one, hb]
    exact DFunLike.congr_fun ((affinePointEquiv eX B).symm_apply_apply (AlgHom.id k B)) b'
  have hsurj := contractionSurjective eA eB δA δB f rfl eB₀ eB₁ hδ hcot.2
  choose a ha using fun α => hsurj (b α)
  let sectionPoint := productPoint x A a l
  let r := (affinePointEquiv eX A).symm sectionPoint
  have hr : f.comp r = AlgHom.id k B := by
    apply (affinePointEquiv eX B).injective
    rw [affinePointEquiv_natural eX m]
    dsimp only [r]
    rw [Equiv.apply_symm_apply, productPoint_map]
    change productPoint x B (fun α => f (a α)) l = b₀
    simp only [ha, hb]
  have hinj := contractionInjective eA eB δA f rfl eA₀ eA₁ hcot.1 r hr
  let E := AlgEquiv.ofBijective f ⟨hinj, hsurj⟩
  let i : A ≅ B := CommAlgCat.isoMk E
  have hi : m = i.hom := rfl
  rw [hi] at hm
  have he : p = eX.inv ≫ (testSpec k).map i.hom.op ≫ eY.hom := by
    rw [hm, Iso.inv_hom_id_assoc]
  rw [he]
  infer_instance

end ContractingProduct

/-- The Borel case follows from the contracting product and the regular-cocharacter
description of the Borel and its unipotent radical. -/
theorem borelRadicalProduct_of_contractingProduct
    (hBorels : BorelsThroughT.{u}) (hRegular : RegularCocharacterBorel.{u})
    (hProduct : ContractingProduct.{u}) : BorelRadicalProduct.{u} := by
  intro k _ G hG T hT hmax B hB hTB
  obtain ⟨cochar, D, hreg, hsame, hsign⟩ := (hBorels G hG T hT hmax).1 B hB hTB
  let e := subgroupIso (A := D.parabolic) (B := B) ⟨hsame.2, hsame.1⟩
  have he : e.val.hom ≫ B.inclusion = D.parabolic.inclusion := e.property
  obtain ⟨_, _, _, _, hrad, _⟩ := hRegular G hG T hT hmax cochar hreg D
  let R := pushSubgroup e.val (contractingSubgroup D)
  refine ⟨R, radical_transport (A := Specs.Unipotent.closedSubgroupAlgebraicGroup D.parabolic)
    (B := Specs.Unipotent.closedSubgroupAlgebraicGroup B) e.val _ hrad, ?_⟩
  intro U l hl
  obtain ⟨p, hp⟩ := ((hProduct G hG T hT hmax).2.2 cochar).2 D U l (hsign ▸ hl)
  refine ⟨p, ?_⟩
  have hinc : R.inclusion ≫ B.inclusion = D.contracting.inclusion := by
    change (D.contractingToParabolic ≫ e.val.hom) ≫ B.inclusion = _
    rw [Category.assoc, he, D.contracting_in_G]
  change p.hom ≫ (underlying k).map R.inclusion ≫ (underlying k).map B.inclusion = _
  rw [← Functor.map_comp, hinc]
  exact hp

private theorem bigCell_of_opposite_eq (G : AffineAlgebraicGroup k) [Smooth G.val.X.hom]
    {c c' : Cocharacter G.val} (h : c' = oppositeCocharacter c)
    (D : LimitDecomposition c) (E : LimitDecomposition c') :
    IsOpenImmersion
      ((fst _ _ ≫ E.contracting.inclusion.hom.hom) *
        (snd _ _ ≫ multiplyFactors D.centralizer.inclusion D.contracting.inclusion)).left := by
  subst c'
  exact bigCell G c D E

/-- In the regular case the two contracting products identify the root cell
map with the open cell of the limit decomposition. -/
theorem regularRootCell_of_contractingProduct
    (hRegular : RegularCocharacterBorel.{u}) (hProduct : ContractingProduct.{u}) :
    RegularRootCell.{u} := by
  intro k _ G hG T hT hmax cochar hreg U negative positive hn hp
  letI := hG.1
  obtain ⟨D⟩ := ((hProduct G hG T hT hmax).2.2 cochar).1
  obtain ⟨E⟩ := ((hProduct G hG T hT hmax).2.2 (oppositeCocharacter cochar)).1
  obtain ⟨p, hpos⟩ := ((hProduct G hG T hT hmax).2.2 cochar).2 D U positive hp
  obtain ⟨n, hneg⟩ := ((hProduct G hG T hT hmax).2.2 (oppositeCocharacter cochar)).2 E U negative hn
  have hsame := (hRegular G hG T hT hmax cochar hreg D).1
  let e := subgroupIso (A := T) (B := D.centralizer) ⟨hsame.2, hsame.1⟩
  let t : T.group.X ≅ D.centralizer.group.X := (underlying k).mapIso e.val
  let j := (tensorIso n (tensorIso t p)).hom
  let m : E.contracting.group.X ⊗ (D.centralizer.group.X ⊗ D.contracting.group.X) ⟶ G.val.X :=
    (fst _ _ ≫ E.contracting.inclusion.hom.hom) *
      (snd _ _ ≫ multiplyFactors D.centralizer.inclusion D.contracting.inclusion)
  have hm : IsOpenImmersion m.left :=
    bigCell_of_opposite_eq G (by simp [oppositeCocharacter, Category.assoc]) D E
  have ht : t.hom ≫ D.centralizer.inclusion.hom.hom = T.inclusion.hom.hom :=
    (Functor.map_comp _ _ _).symm.trans (congrArg (underlying k).map e.property)
  have hinner :
      (t.hom ⊗ₘ p.hom) ≫ multiplyFactors D.centralizer.inclusion D.contracting.inclusion =
        (fst _ _ ≫ T.inclusion.hom.hom) * (snd _ _ ≫ rootProduct U positive) := by
    simp only [multiplyFactors, MonObj.comp_mul, ← Category.assoc, tensorHom_fst, tensorHom_snd]
    simp only [Category.assoc, ht, hpos]
  have hmap : j ≫ m = rootCellMap T U negative positive := by
    change (n.hom ⊗ₘ (t.hom ⊗ₘ p.hom)) ≫ m = rootCellMap T U negative positive
    unfold m rootCellMap
    rw [MonObj.comp_mul, ← Category.assoc, tensorHom_fst,
      ← Category.assoc, tensorHom_snd, Category.assoc, Category.assoc, hneg, hinner]
  rw [← hmap]
  change IsOpenImmersion (j.left ≫ m.left)
  haveI : IsIso j.left := inferInstanceAs (IsIso ((Over.forget _).map j))
  infer_instance

/-- The ordered contracting product under the current Borel premises. -/
theorem contractingProduct_conditional
    (_hBorels : BorelsThroughT.{u})
    (_hConjugacy : GeometricBorelChamberConjugacy.{u})
    (_hGeometric : GeometricBorelRootSubgroups.{u})
    (_hPositivity : PositiveSystemsFromCocharacters.{u})
    (_hRegular : RegularCocharacterBorel.{u}) :
    ContractingProduct.{u} := by
  intro k _ G hG T hT hmax
  obtain ⟨hf, hU, hD⟩ := contractingProduct_exists rootDimension rootSubgroups G hG T hT hmax
  refine ⟨hf, hU, fun c => ⟨hD c, ?_⟩⟩
  intro D U l hl
  let x (α : Root T) := Classical.choice (rootCoordinate_exists rootSubgroups G hG T hT hmax U α)
  obtain ⟨p, hp⟩ := rootProduct_factors (U := U) D l
    (fun α ha => rootSubgroup_embeds (x α) c D ((hl.2 α).mp ha))
  letI := contracting_product_isIso rootSubgroups hG hT hmax x c D l hl p hp
  exact ⟨asIso p, hp⟩

/-- The ordered parametrization for the radical of a Borel through the split torus. -/
theorem borelRadicalProduct_conditional
    (hBorels : BorelsThroughT.{u})
    (hConjugacy : GeometricBorelChamberConjugacy.{u})
    (hGeometric : GeometricBorelRootSubgroups.{u})
    (hPositivity : PositiveSystemsFromCocharacters.{u})
    (hRegular : RegularCocharacterBorel.{u}) :
    BorelRadicalProduct.{u} :=
  borelRadicalProduct_of_contractingProduct hBorels hRegular
    (contractingProduct_conditional hBorels hConjugacy hGeometric hPositivity hRegular)

/-- The product of the negative root groups, the torus, and the positive root
groups is open for a regular cocharacter. -/
theorem regularRootCell_conditional
    (hBorels : BorelsThroughT.{u})
    (hConjugacy : GeometricBorelChamberConjugacy.{u})
    (hGeometric : GeometricBorelRootSubgroups.{u})
    (hPositivity : PositiveSystemsFromCocharacters.{u})
    (hRegular : RegularCocharacterBorel.{u}) :
    RegularRootCell.{u} :=
  regularRootCell_of_contractingProduct hRegular
    (contractingProduct_conditional hBorels hConjugacy hGeometric hPositivity hRegular)

end

end LinearAlgebraicGroups.RootData.OrderedRootProducts

universe v8_closure_7517d3d9a144c623_u0
theorem _root_.«LinearAlgebraicGroups».«RootData».«OrderedRootProducts».«borelRadicalProduct» : _root_.«LinearAlgebraicGroups».«Specs».«OrderedRootProducts».«BorelRadicalProduct».{v8_closure_7517d3d9a144c623_u0} :=
  @_root_.«LinearAlgebraicGroups».«RootData».«OrderedRootProducts».«borelRadicalProduct_conditional».{v8_closure_7517d3d9a144c623_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«borelsThroughT».{v8_closure_7517d3d9a144c623_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«geometricBorelChamberConjugacy».{v8_closure_7517d3d9a144c623_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«geometricBorelRootSubgroups».{v8_closure_7517d3d9a144c623_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«positiveSystemsFromCocharacters».{v8_closure_7517d3d9a144c623_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«regularCocharacterBorel».{v8_closure_7517d3d9a144c623_u0})
theorem _root_.«LinearAlgebraicGroups».«RootData».«OrderedRootProducts».«contractingProduct» : _root_.«LinearAlgebraicGroups».«Specs».«OrderedRootProducts».«ContractingProduct».{v8_closure_7517d3d9a144c623_u0} :=
  @_root_.«LinearAlgebraicGroups».«RootData».«OrderedRootProducts».«contractingProduct_conditional».{v8_closure_7517d3d9a144c623_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«borelsThroughT».{v8_closure_7517d3d9a144c623_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«geometricBorelChamberConjugacy».{v8_closure_7517d3d9a144c623_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«geometricBorelRootSubgroups».{v8_closure_7517d3d9a144c623_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«positiveSystemsFromCocharacters».{v8_closure_7517d3d9a144c623_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«regularCocharacterBorel».{v8_closure_7517d3d9a144c623_u0})
theorem _root_.«LinearAlgebraicGroups».«RootData».«OrderedRootProducts».«regularRootCell» : _root_.«LinearAlgebraicGroups».«Specs».«OrderedRootProducts».«RegularRootCell».{v8_closure_7517d3d9a144c623_u0} :=
  @_root_.«LinearAlgebraicGroups».«RootData».«OrderedRootProducts».«regularRootCell_conditional».{v8_closure_7517d3d9a144c623_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«borelsThroughT».{v8_closure_7517d3d9a144c623_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«geometricBorelChamberConjugacy».{v8_closure_7517d3d9a144c623_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«geometricBorelRootSubgroups».{v8_closure_7517d3d9a144c623_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«positiveSystemsFromCocharacters».{v8_closure_7517d3d9a144c623_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«regularCocharacterBorel».{v8_closure_7517d3d9a144c623_u0})
