import Specs.LinearAlgebraicGroups.RootData.SchemeCentre
import Specs.LinearAlgebraicGroups.RootData.OrderedRootProducts
import LinearAlgebraicGroups.RootData.CharacterPairing
import LinearAlgebraicGroups.Solvable.WordDomainGeometry
import LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic.Group
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.RootData.OrderedRootProducts
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.RootData.SchemeCentre

open _root_.LinearAlgebraicGroups.Specs
open Specs.SchemeCentre (rootLattice)
open Specs.CharacterDescent (Character Cocharacter StandardLattice)
open Specs.CharacterPairing (absoluteRoots adjointWeightVectors characterValue)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap diagonalClosedInclusion
  IntegerCharacters integerGenerator)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.RootGroups (AdditiveLine rootPoint IsRootSubgroup)
open Specs.OrderedRootProducts
open Specs.BorelsAndChambers (IsRegular positiveRoots)
open Specs.AdjointRepresentation (GroupPoints dualMap constants scale)
open private splitPresentation charactersOfIso isTorus_of_split characterValue_monomial
  from LinearAlgebraicGroups.RootData.CharacterPairing
open private comp_conjugateFamily centralizes_iff mono_over from LinearAlgebraicGroups.Affine.Stabilizers
open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private standardLatticeDomain from LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies
open private irreducible_of_geometricallyConnected from LinearAlgebraicGroups.Solvable.WordDomainGeometry

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {k : Type u} [Field k]
variable {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}

private theorem exists_integral_regular {V I : Type u} [AddCommGroup V] [Module ℤ V]
    (f : I → V →ₗ[ℤ] ℤ) (s : Finset I) (hf : ∀ i ∈ s, f i ≠ 0) :
    ∃ v : V, ∀ i ∈ s, f i v ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨v, hv⟩ := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    obtain ⟨w, hw⟩ : ∃ w, f i w ≠ 0 := by
      by_contra! h
      exact hf i (Finset.mem_insert_self _ _) (LinearMap.ext h)
    let bad (j : I) : Set ℤ := {n | f j v + n * f j w = 0}
    have hfinite (j : I) (hj : j ∈ insert i s) : (bad j).Finite := by
      by_cases h : f j w = 0
      · have hj' : j ∈ s := (Finset.mem_insert.mp hj).resolve_left
          (fun e => hw (e ▸ h))
        have he : bad j = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun n hn =>
          hv j hj' (by simpa [bad, h] using hn)
        rw [he]
        exact Set.finite_empty
      · apply Set.Subsingleton.finite
        intro m hm n hn
        apply mul_right_cancel₀ h
        change f j v + m * f j w = 0 at hm
        change f j v + n * f j w = 0 at hn
        exact add_left_cancel (hm.trans hn.symm)
    obtain ⟨n, hn⟩ := (Set.Finite.biUnion (insert i s).finite_toSet
      (fun j hj => hfinite j hj)).exists_notMem
    refine ⟨v + n • w, fun j hj hz => hn ?_⟩
    refine Set.mem_iUnion₂.mpr ⟨j, hj, ?_⟩
    change f j v + n * f j w = 0
    simpa only [map_add, map_zsmul, Int.zsmul_eq_mul] using hz

private theorem exists_regular (hT : IsSplitTorus T.group) (hfin : (absoluteRoots T).Finite) :
    ∃ cochar : Cocharacter T.group, IsRegular T cochar := by
  classical
  obtain ⟨hcomm, h⟩ := LinearAlgebraicGroups.RootData.CharacterPairing.perfectCharacterPairing
    T.group hT
  letI := hcomm
  obtain ⟨_, _, _, _, P, hP, hpair⟩ := h
  letI : Finite (AbstractPairing.Root T) := hfin.to_subtype
  letI := Fintype.ofFinite (AbstractPairing.Root T)
  have hn (α : AbstractPairing.Root T) : P (Additive.ofMul α.val) ≠ 0 := by
    intro hz
    have hx := hP.bijective_left.injective (hz.trans P.map_zero.symm)
    exact α.property.1 (congrArg Additive.toMul hx)
  obtain ⟨v, hv⟩ := exists_integral_regular (fun α : AbstractPairing.Root T =>
    P (Additive.ofMul α.val)) Finset.univ (fun α _ => hn α)
  refine ⟨v.toMul, fun α => ?_⟩
  exact (hpair (Additive.ofMul α.val) v) ▸ hv α (Finset.mem_univ _)

private theorem exists_enumeration (S : Set (AbstractPairing.Root T))
    (hfin : (absoluteRoots T).Finite) : ∃ l, Enumerates l S := by
  classical
  letI : Finite (AbstractPairing.Root T) := hfin.to_subtype
  let s := S.toFinite.toFinset
  exact ⟨s.toList, Finset.nodup_toList _, by simp [s]⟩

private theorem eq_of_precomp_dense {X Y Z : SchemeOver k} {f : X ⟶ Y}
    [IsSchemeTheoreticallyDominant f.left] {a b : Y ⟶ Z} [IsSeparated Z.hom]
    (h : f ≫ a = f ≫ b) : a = b := by
  let e := equalizer.ι a b
  let q := equalizer.lift f h
  have he : q.left ≫ e.left = f.left :=
    congrArg Over.Hom.left (equalizer.lift_ι f h)
  have hker : e.left.ker ≤ f.left.ker := by
    rw [← he]
    exact q.left.le_ker_comp e.left
  haveI : IsClosedImmersion e.left := inferInstanceAs
    (IsClosedImmersion (equalizer.ι a b).left)
  haveI : IsIso e.left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
    (le_bot_iff.mp (f.left.ker_eq_bot ▸ hker))
  haveI : IsIso ((Over.forget (Spec (CommRingCat.of k))).map e) :=
    inferInstanceAs (IsIso e.left)
  haveI : IsIso e := isIso_of_reflects_iso e (Over.forget _)
  exact (cancel_epi e).mp (equalizer.condition a b)

private theorem dense_cell {X : SchemeOver k} (f : X ⟶ G.val.X)
    (hG : IsReductive G) (hf : IsOpenImmersion f.left) [Nonempty X.left] :
    IsSchemeTheoreticallyDominant f.left := by
  letI := G.property.2.1
  letI := G.property.2.2
  letI := hG.1
  letI := hG.2.1
  haveI := irreducible_of_geometricallyConnected G.val
  haveI := isReduced_of_smooth_over_field
    G.val.X.hom
  haveI : IsOpenImmersion f.left := hf
  haveI : IsDominant f.left := ⟨f.left.isOpenEmbedding.isOpen_range.dense
    (Set.range_nonempty _)⟩
  exact IsSchemeTheoreticallyDominant.of_isDominant f.left

private theorem root_product_commutes (U : RootSubgroupFamily T)
    {X : SchemeOver k} (z : X ⟶ G.val.X) (l : List (AbstractPairing.Root T))
    (h : ∀ α ∈ l, Centralizes (U α).val.inclusion z)
    {Y : SchemeOver k} (y : Y ⟶ X) (x : Y ⟶ product (fun α => (U α).val.group.X) l) :
    Commute (y ≫ z) (x ≫ rootProduct U l) := by
  induction l with
  | nil =>
      change Commute (y ≫ z) (x ≫ (1 : _ ⟶ G.val.X))
      rw [MonObj.comp_one]
      exact Commute.one_right _
  | cons α l ih =>
      change Commute (y ≫ z)
        (x ≫ ((fst _ _ ≫ (U α).val.inclusion.hom.hom) * (snd _ _ ≫ rootProduct U l)))
      rw [MonObj.comp_mul]
      exact ((centralizes_iff _ _).mp (h α (List.mem_cons_self ..)) Y y
        (x ≫ fst _ _)).mul_right
        (ih (fun β hb => h β (List.mem_cons_of_mem _ hb)) (x ≫ snd _ _))

private def root_product_identity (U : RootSubgroupFamily T) (X : SchemeOver k) :
    (l : List (AbstractPairing.Root T)) → X ⟶ product (fun α => (U α).val.group.X) l
  | [] => toUnit X
  | _ :: l => lift 1 (root_product_identity U X l)

private theorem dense_whisker {X Y : SchemeOver k} (f : X ⟶ Y) (S : SchemeOver k)
    [IsSchemeTheoreticallyDominant f.left] [QuasiCompact f.left] :
    IsSchemeTheoreticallyDominant (f ▷ S).left := by
  have hfst {a b : X.left ⟶ Spec (CommRingCat.of k)} (h : a = b) :
      eqToHom (congrArg (fun g => pullback g S.hom) h) ≫ pullback.fst b S.hom =
        pullback.fst a S.hom := by subst b; simp
  have hsnd {a b : X.left ⟶ Spec (CommRingCat.of k)} (h : a = b) :
      eqToHom (congrArg (fun g => pullback g S.hom) h) ≫ pullback.snd b S.hom =
        pullback.snd a S.hom := by subst b; simp
  let e : (X ⊗ S).left = pullback (f.left ≫ Y.hom) S.hom :=
    congrArg (fun g => pullback g S.hom) f.w.symm
  let i : (X ⊗ S).left ≅ pullback f.left (pullback.fst Y.hom S.hom) :=
    eqToIso e ≪≫ (pullbackRightPullbackFstIso Y.hom S.hom f.left).symm
  have hi : (f ▷ S).left = i.hom ≫ pullback.snd _ _ := by
    have hh : i.hom = eqToHom e ≫ (pullbackRightPullbackFstIso Y.hom S.hom f.left).inv := rfl
    apply pullback.hom_ext
    · rw [Over.whiskerRight_left_fst, hh, Category.assoc, Category.assoc,
        pullbackRightPullbackFstIso_inv_snd_fst, ← Category.assoc, hfst f.w.symm]
    · rw [Over.whiskerRight_left_snd, hh, Category.assoc, Category.assoc,
        pullbackRightPullbackFstIso_inv_snd_snd, hsnd f.w.symm]
  rw [hi]
  infer_instance

private theorem centralizes_of_cell
    (cell : RegularRootCell.{u}) (contract : ContractingProduct.{u})
    (hG : IsReductive G) (hT : IsSplitTorus T.group) (hmax : IsGeometricallyMaximal T)
    {X : SchemeOver k} (z : X ⟶ G.val.X)
    (ht : Centralizes T.inclusion z)
    (hu : ∀ (α : AbstractPairing.Root T) (U : ClosedSubgroup G.val),
      IsRootSubgroup T U α.val → Centralizes U.inclusion z) :
    Centralizes (𝟙 G.val) z := by
  obtain ⟨hfin, ⟨U⟩, _⟩ := contract G hG T hT hmax
  obtain ⟨cochar, hcochar⟩ := exists_regular hT hfin
  obtain ⟨l, hl⟩ := exists_enumeration (positiveRoots T (CocharacterDynamics.oppositeCocharacter cochar)) hfin
  obtain ⟨m, hm⟩ := exists_enumeration (positiveRoots T cochar) hfin
  let f := rootCellMap T U l m
  haveI : IsOpenImmersion f.left := cell G hG T hT hmax cochar hcochar U l m hl hm
  let S := 𝟙_ (SchemeOver k)
  let p : S ⟶ _ := lift (root_product_identity U S l)
    (lift (1 : S ⟶ T.group.X) (root_product_identity U S m))
  haveI : Nonempty (product (fun α => (U α).val.group.X) l ⊗
      (T.group.X ⊗ product (fun α => (U α).val.group.X) m)).left :=
    ⟨p.left (IsLocalRing.closedPoint k)⟩
  haveI := dense_cell f hG inferInstance
  haveI : QuasiCompact f.left := by
    letI := G.property.1
    letI := T.isClosedImmersion
    haveI : IsAffine T.group.X.left := isAffine_of_isAffineHom T.inclusion.hom.hom.left
    have affineProd (n : List (AbstractPairing.Root T)) :
        IsAffine (product (fun α => (U α).val.group.X) n).left := by
      induction n with
      | nil => exact inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
      | cons a n ih =>
        haveI := (U a).val.isClosedImmersion
        haveI : IsAffine (U a).val.group.X.left :=
          isAffine_of_isAffineHom (U a).val.inclusion.hom.hom.left
        exact inferInstanceAs (IsAffine (pullback (U a).val.group.X.hom (product _ n).hom))
    haveI := affineProd l
    haveI := affineProd m
    haveI : IsAffine (T.group.X ⊗ product (fun α => (U α).val.group.X) m).left :=
      inferInstanceAs (IsAffine (pullback T.group.X.hom (product _ m).hom))
    haveI : IsAffine (product (fun α => (U α).val.group.X) l ⊗
        (T.group.X ⊗ product (fun α => (U α).val.group.X) m)).left :=
      inferInstanceAs (IsAffine (pullback (product _ l).hom (_ ⊗ _ : SchemeOver k).hom))
    exact inferInstance
  haveI := dense_whisker f X
  haveI := G.property.1
  haveI : IsSeparated G.val.X.hom := inferInstance
  let negativeFactors := product (fun α => (U α).val.group.X) l
  let positiveFactors := product (fun α => (U α).val.group.X) m
  let cellDomain := negativeFactors ⊗ (T.group.X ⊗ positiveFactors)
  let baseProjection : cellDomain ⊗ X ⟶ X := snd cellDomain X
  let negativeProjection : cellDomain ⊗ X ⟶ negativeFactors := fst cellDomain X ≫ fst _ _
  let torusProjection : cellDomain ⊗ X ⟶ T.group.X := fst cellDomain X ≫ snd _ _ ≫ fst _ _
  let positiveProjection : cellDomain ⊗ X ⟶ positiveFactors := fst cellDomain X ≫ snd _ _ ≫ snd _ _
  have hnegative := root_product_commutes U z l
    (fun α _ => hu α (U α).val (U α).property) baseProjection negativeProjection
  have htorus := (centralizes_iff _ _).mp ht _ baseProjection torusProjection
  have hpositive := root_product_commutes U z m
    (fun α _ => hu α (U α).val (U α).property) baseProjection positiveProjection
  have hcomm : Commute (baseProjection ≫ z) (fst cellDomain X ≫ f) := by
    simpa only [f, rootCellMap, MonObj.comp_mul, Category.assoc,
      negativeProjection, torusProjection, positiveProjection]
      using hnegative.mul_right (htorus.mul_right hpositive)
  unfold Centralizes
  apply eq_of_precomp_dense (f := f ▷ X)
  simpa only [conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc,
    whiskerRight_fst_assoc, whiskerRight_snd_assoc, whiskerRight_fst, whiskerRight_snd,
    Grp.id_hom_hom, Category.comp_id, baseProjection] using mul_inv_eq_iff_eq_mul.mpr hcomm.eq

open private conjugateLe_iff from LinearAlgebraicGroups.Affine.Stabilizers
open WithConv

private abbrev affinePoint {A : Type u} [CommRing A] [Algebra k A] {R : TestAlgebra k}
    (f : A →ₐ[k] R) : Points ((testSpec k).obj (op (CommAlgCat.of k A))) R :=
  (testSpec k).map (CommAlgCat.ofHom f).op

private theorem rootPoint_inj {A : AdditiveLine k} {U : ClosedSubgroup G.val}
    (x : A.group ≅ U.group) (R : TestAlgebra k) :
    Function.Injective (rootPoint (x.hom ≫ U.inclusion) R) := by
  letI : Mono U.inclusion.hom.hom := mono_over _ U.isClosedImmersion
  intro a b h
  change affinePoint (Polynomial.aeval a) ≫ x.hom.hom.hom ≫ U.inclusion.hom.hom =
    affinePoint (Polynomial.aeval b) ≫ x.hom.hom.hom ≫ U.inclusion.hom.hom at h
  have he : affinePoint (Polynomial.aeval a) = affinePoint (Polynomial.aeval b) := by
    simpa only [← Category.assoc, cancel_mono, Grp.comp_hom_hom] using h
  have hc := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective he
  simpa using congrArg (fun f => f.unop.hom Polynomial.X) hc

private theorem rootPoint_surj {A : AdditiveLine k} {H : GroupScheme k}
    (x : A.group ≅ H) (R : TestAlgebra k) :
    Function.Surjective (rootPoint x.hom R) := by
  intro y
  let f := (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage (y ≫ x.inv.hom.hom)
  refine ⟨f.unop.hom Polynomial.X, ?_⟩
  have hf : CommAlgCat.ofHom (Polynomial.aeval (f.unop.hom Polynomial.X)) = f.unop := by
    apply CommAlgCat.hom_ext
    exact Polynomial.algHom_ext (Polynomial.aeval_X _)
  change (testSpec k).map (CommAlgCat.ofHom (Polynomial.aeval (f.unop.hom Polynomial.X))).op ≫
    x.hom.hom.hom = y
  rw [hf, Quiver.Hom.op_unop, Functor.FullyFaithful.map_preimage, Category.assoc]
  rw [← Grp.comp_hom_hom, Iso.inv_hom_id]
  rfl

private theorem rootPoint_map {A : AdditiveLine k} {H : GroupScheme k} (x : A.group ⟶ H)
    {R S : TestAlgebra k} (f : R ⟶ S) (a : R) :
    mapPoints f (rootPoint x R a) = rootPoint x S (f.hom a) := by
  simp only [mapPoints, rootPoint, ← Category.assoc, ← Functor.map_comp, ← op_comp]
  congr 2
  exact congrArg Quiver.Hom.op (CommAlgCat.hom_ext (Polynomial.algHom_ext (by
    change f.hom (Polynomial.aeval a Polynomial.X) = Polynomial.aeval (f.hom a) Polynomial.X
    simp only [Polynomial.aeval_X])))

private theorem rootPoint_zero {A : AdditiveLine k} {H : GroupScheme k}
    (x : A.group ⟶ H) (R : TestAlgebra k) :
    rootPoint x R 0 = 1 := by
  letI := A.operations.hopf
  let D : HopfAlgebraCategory k := CommHopfAlgCat.of k (Polynomial k)
  have h : (Polynomial.aeval (0 : R) : Polynomial k →ₐ[k] R) =
      (1 : WithConv (Polynomial k →ₐ[k] R)).ofConv := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X]
    change 0 = algebraMap k R (A.operations.epsilon Polynomial.X)
    rw [A.counit, map_zero]
  change affinePoint (Polynomial.aeval (0 : R)) ≫ x.hom.hom = 1
  rw [h]
  change ((((hopfSpecPointIso D).hom.app R) 1 : GroupPoints A.group R) ≫ x.hom.hom) = 1
  rw [map_one, MonObj.one_comp]

/-- Over the universal torus point, normalized conjugation on the additive
line is given by one polynomial, with arbitrary test-ring specialization. -/
private theorem root_conjugation_polynomial {A : AdditiveLine k} {U : ClosedSubgroup G.val}
    (x : A.group ≅ U.group) (hn : Normalizes U.inclusion T.inclusion.hom.hom)
    {B : TestAlgebra k} (t : GroupPoints T.group B) :
    ∃ p : Polynomial B, ∀ {R : TestAlgebra k} (f : B ⟶ R) (a : R),
      let g : GroupPoints G.val R := mapPoints f t ≫ T.inclusion.hom.hom
      g * rootPoint (x.hom ≫ U.inclusion) R a * g⁻¹ =
        rootPoint (x.hom ≫ U.inclusion) R (Polynomial.aevalTower f.hom a p) := by
  let P := CommAlgCat.of k (Polynomial B)
  let j : B ⟶ P := CommAlgCat.ofHom (IsScalarTower.toAlgHom k B (Polynomial B))
  have hle := ((LinearAlgebraicGroups.normalizesIff k U.inclusion
    U.isClosedImmersion _ _).mp hn).1
  obtain ⟨q, hq⟩ := (conjugateLe_iff _ _).mp hle ((testSpec k).obj (op P)) (mapPoints j t)
    (rootPoint x.hom P Polynomial.X)
  obtain ⟨p, rfl⟩ := rootPoint_surj x P q
  refine ⟨p, ?_⟩
  intro R f a
  let b : P ⟶ R := CommAlgCat.ofHom (Polynomial.aevalTower f.hom a)
  have hf : j ≫ b = f := CommAlgCat.hom_ext (Polynomial.aevalTower_comp_toAlgHom f.hom a)
  have he := congrArg (((groupPointsFunctor k).obj G.val).map b).hom hq.symm
  simp only [map_mul, map_inv] at he
  change
    mapPoints b (mapPoints j t ≫ T.inclusion.hom.hom) *
      mapPoints b (rootPoint (x.hom ≫ U.inclusion) P Polynomial.X) *
      (mapPoints b (mapPoints j t ≫ T.inclusion.hom.hom))⁻¹ =
    mapPoints b (rootPoint (x.hom ≫ U.inclusion) P p) at he
  have ht : mapPoints b (mapPoints j t ≫ T.inclusion.hom.hom) =
      mapPoints f t ≫ T.inclusion.hom.hom := by
    simp only [mapPoints, ← Category.assoc, ← Functor.map_comp, ← op_comp, hf]
  rw [ht, rootPoint_map, rootPoint_map] at he
  have hx : b.hom (Polynomial.X : Polynomial B) = a := Polynomial.aevalTower_X f.hom a
  rw [hx] at he
  exact he

private theorem root_conjugation_linear {A : AdditiveLine k} {U : ClosedSubgroup G.val}
    (x : A.group ≅ U.group) (hn : Normalizes U.inclusion T.inclusion.hom.hom)
    {B : TestAlgebra k} [IsDomain B] (t : GroupPoints T.group B) :
    ∃ c : B, ∀ {R : TestAlgebra k} (f : B ⟶ R) (a : R),
      let g : GroupPoints G.val R := mapPoints f t ≫ T.inclusion.hom.hom
      g * rootPoint (x.hom ≫ U.inclusion) R a * g⁻¹ =
        rootPoint (x.hom ≫ U.inclusion) R (f.hom c * a) := by
  obtain ⟨p, hp⟩ := root_conjugation_polynomial x hn t
  obtain ⟨q, hq⟩ := root_conjugation_polynomial x hn t⁻¹
  let P := CommAlgCat.of k (Polynomial B)
  let j : B ⟶ P := CommAlgCat.ofHom (IsScalarTower.toAlgHom k B (Polynomial B))
  have hj (a b : Polynomial B) : Polynomial.aevalTower j.hom a b = b.comp a := by
    change Polynomial.aevalTower (Algebra.ofId B (Polynomial B)) a b = _
    rw [Polynomial.aevalTower_ofId]
    exact Polynomial.aeval_def _ _
  have hcomp : p.comp q = Polynomial.X := by
    have hp' := hp j q
    have hq' := hq j (Polynomial.X : Polynomial B)
    simp only [hj, Polynomial.comp_X] at hp' hq'
    let g : GroupPoints G.val P := mapPoints j t ≫ T.inclusion.hom.hom
    have hm : mapPoints j (t⁻¹ : GroupPoints T.group B) ≫ T.inclusion.hom.hom = g⁻¹ := by
      exact (map_inv
        ((((groupPointsFunctor k).map T.inclusion).app P).hom.comp
          (((groupPointsFunctor k).obj T.group).map j).hom) t)
    rw [hm, inv_inv] at hq'
    apply rootPoint_inj x P
    rw [← hp', ← hq']
    change g * (g⁻¹ * _ * g) * g⁻¹ = _
    group
  have hdeg : p.natDegree = 1 := by
    have h := congrArg Polynomial.natDegree hcomp
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_X] at h
    exact Nat.eq_one_of_mul_eq_one_right h
  have hzero : p.coeff 0 = 0 := by
    have h := hp (𝟙 B) (0 : B)
    have hEval : Polynomial.aevalTower (CommAlgCat.Hom.hom (𝟙 B)) (0 : B) p = p.coeff 0 := by
      exact (Polynomial.coeff_zero_eq_eval_zero p).symm
    let g : GroupPoints G.val B := mapPoints (𝟙 B) t ≫ T.inclusion.hom.hom
    have hh : g * rootPoint (x.hom ≫ U.inclusion) B 0 * g⁻¹ =
        rootPoint (x.hom ≫ U.inclusion) B (p.coeff 0) :=
      h.trans (congrArg (rootPoint (x.hom ≫ U.inclusion) B) hEval)
    rw [rootPoint_zero, mul_one, mul_inv_cancel] at hh
    exact rootPoint_inj x B (hh.symm.trans (rootPoint_zero _ _).symm)
  refine ⟨p.coeff 1, ?_⟩
  intro R f a
  have he := Polynomial.eq_X_add_C_of_natDegree_le_one hdeg.le
  rw [hzero, Polynomial.C_0, add_zero] at he
  have hn : Polynomial.aevalTower f.hom a p = f.hom (p.coeff 1) * a :=
    (congrArg (Polynomial.aevalTower f.hom a) he).trans
      (by rw [map_mul, Polynomial.aevalTower_C, Polynomial.aevalTower_X])
  exact (hp f a).trans (congrArg (rootPoint (x.hom ≫ U.inclusion) R) hn)

private theorem characterValue_naturality {H : GroupScheme k} (χ : Character H)
    {R S : TestAlgebra k} (b : R ⟶ S) (t : GroupPoints H R) :
    characterValue χ S (mapPoints b t) = b.hom (characterValue χ R t) := by
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let p := t ≫ χ.hom.hom
  let c := F.preimage p
  have hp : (testSpec k).map c = p := F.map_preimage p
  unfold characterValue
  dsimp only
  change (F.preimage ((testSpec k).map b.op ≫ t ≫ χ.hom.hom)).unop.hom _ = b.hom (c.unop.hom _)
  rw [← show (testSpec k).map c = t ≫ χ.hom.hom from hp,
    ← Functor.map_comp, Functor.FullyFaithful.preimage_map]
  rfl

private theorem root_action {U : ClosedSubgroup G.val} {α : Character T.group}
    (hT : IsSplitTorus T.group) (hU : IsRootSubgroup T U α) :
    ∃ (A : AdditiveLine k) (x : A.group ≅ U.group),
      Specs.RootGroups.HasScalarAction T α (x.hom ≫ U.inclusion) := by
  obtain ⟨ops, hΔ, hε, hι, ⟨x₀⟩⟩ := hU.2.1
  let A : AdditiveLine k := ⟨ops, hΔ, hε, hι⟩
  let x : A.group ≅ U.group := x₀.symm
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation hT
  let B := CommAlgCat.of k (MonoidAlgebra k (StandardLattice.{u} r))
  letI : IsDomain B := standardLatticeDomain r
  let t : GroupPoints T.group B := i.hom.hom.hom
  obtain ⟨c, hc⟩ := root_conjugation_linear x hU.2.2.1 t
  let K := CommAlgCat.of k k
  let D := CommAlgCat.of k (DualNumber B)
  let ε (R : Type u) [CommRing R] : DualNumber R := ⟨0, 1⟩
  let v : Lie k U.group := Additive.ofMul ⟨rootPoint x.hom (CommAlgCat.of k (DualNumber k)) (ε k),
    by
      change mapPoints (dualReduction k) (rootPoint x.hom _ (ε k)) = 1
      rw [rootPoint_map]
      exact rootPoint_zero x.hom K⟩
  let y := x.hom ≫ U.inclusion
  have hv : mapPointKernel U.inclusion v ∈ adjointWeightVectors T α :=
    hU.2.2.2 ⟨v, rfl⟩
  have hw := hv B t
  let g : Points G.val.X D := mapPoints (constants B) t ≫ T.inclusion.hom.hom
  let extendDual : CommAlgCat.of k (DualNumber k) ⟶ D :=
    dualMap (CommAlgCat.ofHom (Algebra.ofId k B))
  have hdual : extendDual.hom (ε k) = ε B :=
    TrivSqZeroExt.ext (by exact map_zero _) (by exact map_one _)
  change g * mapPoints extendDual (rootPoint y _ (ε k)) * g⁻¹ =
    mapPoints (scale B (characterValue α B t))
      (mapPoints extendDual (rootPoint y _ (ε k))) at hw
  rw [rootPoint_map, hdual, rootPoint_map] at hw
  have hcalc := hc (constants B) (ε B)
  have hce := rootPoint_inj x D (hcalc.symm.trans hw)
  have he : c = characterValue α B t := by
    have hs := congrArg (fun a : DualNumber B => a.snd) hce
    simpa [ε, constants, scale] using hs
  refine ⟨A, x, fun R z a => ?_⟩
  obtain ⟨f, hf⟩ := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_surjective
    (z ≫ i.inv.hom.hom)
  have hzt : mapPoints f.unop t = z := by
    change (testSpec k).map f ≫ i.hom.hom.hom = z
    rw [hf, Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id]
    rfl
  have hh := hc f.unop a
  simpa only [he, ← characterValue_naturality, hzt] using hh

open LinearAlgebraicGroups.DiagonalizableGroups (groupAlgebraPointsIso)
open private pointsIso_precompose pointsIso_spec integerHomEquiv specIso
  groupAlgebraMap_surjective from LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private specGroupMap_comp from LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem monomial_eval {M : Type u} [CommGroup M] (R : TestAlgebra k)
    (t : GroupPoints (specGroup (groupAlgebra k M)) R) (α : M) :
    (t ≫ (specGroupMap (groupAlgebraMap k (integerHomEquiv M α))).hom.hom = 1) ↔
      (show M →* Rˣ from (groupAlgebraPointsIso k M).hom.app R t) α = 1 := by
  let p := (groupAlgebraPointsIso k IntegerCharacters).hom.app R
  have hp : Function.Injective p := (ConcreteCategory.bijective_of_isIso p).1
  constructor
  · intro h
    have hh := congrArg (fun (z : GroupPoints (specGroup (groupAlgebra k IntegerCharacters)) R) =>
      (show IntegerCharacters →* Rˣ from p z) integerGenerator) h
    rw [show (show IntegerCharacters →* Rˣ from p (1 : GroupPoints _ R)) integerGenerator = 1
      from congrArg (fun f : IntegerCharacters →* Rˣ => f integerGenerator) (map_one p.hom)] at hh
    change (show IntegerCharacters →* Rˣ from
      (groupAlgebraPointsIso k IntegerCharacters).hom.app R
      (((groupPointsFunctor k).map (specGroupMap (groupAlgebraMap k (integerHomEquiv M α)))).app R t))
      integerGenerator = 1 at hh
    simpa only [pointsIso_precompose, show (integerHomEquiv M α) integerGenerator = α from zpow_one α] using hh
  · intro h
    apply hp
    rw [map_one]
    change (show IntegerCharacters →* Rˣ from p _) = 1
    apply (integerHomEquiv (Rˣ)).symm.injective
    change (show IntegerCharacters →* Rˣ from
      (groupAlgebraPointsIso k IntegerCharacters).hom.app R
      (((groupPointsFunctor k).map (specGroupMap (groupAlgebraMap k (integerHomEquiv M α)))).app R t))
      integerGenerator = 1
    simpa only [pointsIso_precompose, show (integerHomEquiv M α) integerGenerator = α from zpow_one α] using h

private theorem split_character_presentation {H : GroupScheme k} (hT : IsSplitTorus H) :
    Group.FG (Character H) ∧
      ∃ e : specGroup (groupAlgebra k (Character H)) ≅ H,
        ∀ α : Character H, e.hom ≫ α =
          specGroupMap (groupAlgebraMap k (integerHomEquiv (Character H) α)) := by
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation hT
  let M := StandardLattice.{u} r
  obtain ⟨χ, _, hχ, _, _⟩ := LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing
    (k := k) r
  let c : M ≃* Character H := χ.trans (charactersOfIso i)
  letI : Group.FG IntegerCharacters.{u} :=
    let e : Multiplicative ℤ ≃* IntegerCharacters.{u} := MulEquiv.ulift.symm
    Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
  letI : Group.FG M := by
    apply Group.fg_def.mpr
    simpa only [Subgroup.pi_top] using
      (Subgroup.FG.pi (P := fun (_ : Fin r) => (⊤ : Subgroup IntegerCharacters)) fun _ =>
        Group.fg_def.mp (inferInstance : Group.FG IntegerCharacters.{u}))
  let q : specGroup (groupAlgebra k (Character H)) ≅ specGroup (groupAlgebra k M) :=
    specIso (MonoidAlgebra.domCongrBialgEquiv k k c)
  refine ⟨Group.fg_of_surjective (f := c.toMonoidHom) c.surjective, q ≪≫ i, ?_⟩
  intro α
  obtain ⟨m, rfl⟩ := c.surjective α
  have hq : q.hom = specGroupMap (groupAlgebraMap k c.toMonoidHom) := rfl
  have hm : χ m = specGroupMap (groupAlgebraMap k (integerHomEquiv M m)) := hχ m
  calc
    (q ≪≫ i).hom ≫ c m = q.hom ≫ χ m := by
      change (q.hom ≫ i.hom) ≫ (i.inv ≫ χ m) = _
      rw [Category.assoc, Iso.hom_inv_id_assoc]
    _ = specGroupMap (groupAlgebraMap k (integerHomEquiv (Character H) (c m))) := by
      rw [hq, hm, ← specGroupMap_comp]
      congr 1
      apply CommHopfAlgCat.hom_ext
      change (MonoidAlgebra.mapDomainBialgHom k c.toMonoidHom).comp
          (MonoidAlgebra.mapDomainBialgHom k (integerHomEquiv M m)) =
        MonoidAlgebra.mapDomainBialgHom k (integerHomEquiv (Character H) (c m))
      rw [← MonoidAlgebra.mapDomainBialgHom_comp]
      apply congrArg (MonoidAlgebra.mapDomainBialgHom k)
      apply MonoidHom.ext
      intro z
      exact map_zpow c m z.down.toAdd

private theorem value_for_presented_character {H : GroupScheme k}
    (e : specGroup (groupAlgebra k (Character H)) ≅ H)
    (he : ∀ α : Character H, e.hom ≫ α =
      specGroupMap (groupAlgebraMap k (integerHomEquiv (Character H) α)))
    (R : TestAlgebra k) (t : GroupPoints H R) (α : Character H) :
    characterValue α R t =
      ((show Character H →* Rˣ from (groupAlgebraPointsIso k (Character H)).hom.app R
        (t ≫ e.inv.hom.hom)) α : R) := by
  let p := (hopfSpecPointIso (groupAlgebra k (Character H))).hom.app R
  obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso p).2 (t ≫ e.inv.hom.hom)
  let ei := (Grp.forget (SchemeOver k)).mapIso e
  have ht : t = affinePoint a.ofConv ≫ ei.hom := by
    let t₀ : Points H.X R := t
    change t₀ = affinePoint a.ofConv ≫ ei.hom
    have hpre : affinePoint a.ofConv = t₀ ≫ ei.inv := ha
    simp only [hpre, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc
    characterValue α R t = a.ofConv (MonoidAlgebra.single α 1) := by
      conv_lhs => rw [ht]
      change characterValue (e.hom ≫ α) R (affinePoint a.ofConv) = _
      rw [he α]
      exact characterValue_monomial R a.ofConv α
    _ = _ := (pointsIso_spec (Character H) R a.ofConv α).symm.trans
      (congrArg (fun s : GroupPoints (specGroup (groupAlgebra k (Character H))) R =>
        ((show Character H →* Rˣ from (groupAlgebraPointsIso k (Character H)).hom.app R s) α).val) ha)

private theorem torus_equations {H : GroupScheme k}
    (e : specGroup (groupAlgebra k (Character H)) ≅ H)
    (he : ∀ α : Character H, e.hom ≫ α =
      specGroupMap (groupAlgebraMap k (integerHomEquiv (Character H) α)))
    (R : TestAlgebra k) (t : GroupPoints H R) (α : Character H) :
    (t ≫ α.hom.hom = 1) ↔ characterValue α R t = 1 := by
  rw [value_for_presented_character e he]
  have ht : t ≫ α.hom.hom =
    (t ≫ e.inv.hom.hom) ≫
      (specGroupMap (groupAlgebraMap k (integerHomEquiv (Character H) α))).hom.hom := by
    rw [← he, Grp.comp_hom_hom]
    let ei := (Grp.forget (SchemeOver k)).mapIso e
    let t₀ : Points H.X R := t
    change t₀ ≫ α.hom.hom = (t₀ ≫ ei.inv) ≫ (ei.hom ≫ α.hom.hom)
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [ht, monomial_eval]
  exact ⟨fun h => congrArg Units.val h, fun h => Units.ext h⟩

private theorem diagonal_root_kernel
    (e : specGroup (groupAlgebra k (Character T.group)) ≅ T.group)
    (he : ∀ α : Character T.group, e.hom ≫ α =
      specGroupMap (groupAlgebraMap k (integerHomEquiv (Character T.group) α)))
    (R : TestAlgebra k) (t : GroupPoints T.group R) :
    (∀ α ∈ absoluteRoots T, t ≫ α.hom.hom = 1) ↔
      ∃ z : GroupPoints (specGroup (groupAlgebra k (Character T.group ⧸ rootLattice T))) R,
        z ≫ ((diagonalClosedInclusion k (rootLattice T)) ≫ e.hom).hom.hom = t := by
  let M := Character T.group
  let N := rootLattice T
  let q := QuotientGroup.mk' N
  let ei := (Grp.forget (SchemeOver k)).mapIso e
  let t' : GroupPoints (specGroup (groupAlgebra k M)) R := t ≫ ei.inv
  let v : M →* Rˣ := (groupAlgebraPointsIso k M).hom.app R t'
  have char (α : M) : (t ≫ α.hom.hom = 1) ↔ v α = 1 := by
    rw [torus_equations e he, value_for_presented_character e he]
    exact ⟨fun h => Units.ext h, fun h => congrArg Units.val h⟩
  have eval (z : GroupPoints (specGroup (groupAlgebra k (M ⧸ N))) R) (m : M) :
      (show M →* Rˣ from (groupAlgebraPointsIso k M).hom.app R
        (z ≫ (diagonalClosedInclusion k N).hom.hom)) m =
        (show (M ⧸ N) →* Rˣ from (groupAlgebraPointsIso k (M ⧸ N)).hom.app R z) (q m) :=
    pointsIso_precompose q R z m
  constructor
  · intro h
    have hN : N ≤ v.ker := (Subgroup.closure_le v.ker).mpr fun m hm => (char m).mp (h m hm)
    let w := QuotientGroup.lift N v hN
    let p := (groupAlgebraPointsIso k (M ⧸ N)).hom.app R
    obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso p).2 w
    have ht : z ≫ (diagonalClosedInclusion k N).hom.hom = t' := by
      apply (ConcreteCategory.bijective_of_isIso ((groupAlgebraPointsIso k M).hom.app R)).1
      apply MonoidHom.ext
      intro m
      exact (eval z m).trans (by rw [show p z = w from hz]; rfl)
    refine ⟨z, ?_⟩
    change z ≫ (diagonalClosedInclusion k N).hom.hom ≫ e.hom.hom.hom = t
    rw [← Category.assoc, ht]
    change (t ≫ ei.inv) ≫ ei.hom = t
    simp
  · rintro ⟨z, hz⟩ m hm
    apply (char m).mpr
    have ht : z ≫ (diagonalClosedInclusion k N).hom.hom = t' := by
      change z ≫ (diagonalClosedInclusion k N).hom.hom ≫ e.hom.hom.hom = t at hz
      change z ≫ (diagonalClosedInclusion k N).hom.hom ≫ ei.hom = t at hz
      let z₀ : Points (specGroup (groupAlgebra k (M ⧸ N))).X R := z
      let t₀ : Points T.group.X R := t
      change z₀ ≫ (diagonalClosedInclusion k N).hom.hom = t₀ ≫ ei.inv
      calc
        _ = ((z₀ ≫ (diagonalClosedInclusion k N).hom.hom) ≫ ei.hom) ≫ ei.inv := by
          simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
        _ = t₀ ≫ ei.inv := congrArg (· ≫ ei.inv) (by simpa only [Category.assoc] using hz)
    change (show M →* Rˣ from (groupAlgebraPointsIso k M).hom.app R t') m = 1
    rw [← ht, eval, show q m = 1 from (QuotientGroup.eq_one_iff m).mpr (Subgroup.subset_closure hm),
      map_one]

private theorem centralizes_precomp {H F : GroupScheme k} {X Y : SchemeOver k}
    {z : Y ⟶ F.X} {i : H ⟶ F} (h : Centralizes i z) (b : X ⟶ Y) :
    Centralizes i (b ≫ z) := by
  apply (centralizes_iff _ _).mpr
  intro P p q
  exact (centralizes_iff _ _).mp h P (p ≫ b) q

private theorem centralizes_torus_of_central {X : SchemeOver k} {z : X ⟶ G.val.X}
    (h : Centralizes (𝟙 G.val) z) : Centralizes T.inclusion z := by
  apply (centralizes_iff _ _).mpr
  intro P p q
  exact (centralizes_iff _ _).mp h P p (q ≫ T.inclusion.hom.hom)

private theorem central_torus_points
    (contract : ContractingProduct.{u}) (cell : RegularRootCell.{u})
    (hG : IsReductive G) (hT : IsSplitTorus T.group) (hmax : IsGeometricallyMaximal T)
    (R : TestAlgebra k) (t : GroupPoints T.group R) :
    Centralizes (𝟙 G.val) (t ≫ T.inclusion.hom.hom) ↔
      ∀ α ∈ absoluteRoots T, characterValue α R t = 1 := by
  let z : GroupPoints G.val R := t ≫ T.inclusion.hom.hom
  have hC := LinearAlgebraicGroups.Reductive.TorusCentralizer.maximalTorusCentralizer
    G hG T (isTorus_of_split hT) hmax
  constructor
  · intro h α hα
    obtain ⟨_, ⟨U⟩, _⟩ := contract G hG T hT hmax
    let W := U ⟨α, hα⟩
    obtain ⟨A, x, hx⟩ := root_action hT W.property
    have hc := (centralizes_iff _ _).mp h _ (𝟙 _)
      (rootPoint (x.hom ≫ W.val.inclusion) R 1)
    have he := hx R t 1
    have hc' : z * rootPoint (x.hom ≫ W.val.inclusion) R 1 * z⁻¹ =
        rootPoint (x.hom ≫ W.val.inclusion) R 1 := by
      apply mul_inv_eq_iff_eq_mul.mpr
      simpa only [Category.id_comp, Grp.id_hom_hom, Category.comp_id] using hc.eq
    simpa only [mul_one] using rootPoint_inj x R (he.symm.trans hc')
  · intro h
    apply centralizes_of_cell cell contract hG hT hmax z
      ((hC _ _).mpr ⟨t, rfl⟩)
    intro α U hU
    obtain ⟨A, x, hx⟩ := root_action hT hU
    letI := G.property.1
    letI := U.isClosedImmersion
    haveI : IsAffine U.group.X.left := isAffine_of_isAffineHom U.inclusion.hom.hom.left
    let base := (testSpec k).obj (op R)
    haveI : IsAffine base.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
    apply hom_ext_of_points (inferInstanceAs (IsAffine (pullback U.group.X.hom base.hom)))
    intro S p
    rw [comp_conjugateFamily]
    let q : (testSpec k).obj (op S) ⟶ base := p ≫ snd _ _
    let w : GroupPoints U.group S := p ≫ fst _ _
    obtain ⟨b, hb⟩ := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_surjective q
    obtain ⟨a, ha⟩ := rootPoint_surj x S w
    have he := hx S (mapPoints b.unop t) a
    have hs := characterValue_naturality α.val b.unop t
    rw [h α.val α.property, map_one] at hs
    rw [hs, one_mul] at he
    have hbase : mapPoints b.unop t = q ≫ t := by
      change (testSpec k).map b.unop.op ≫ t = q ≫ t
      rw [Quiver.Hom.op_unop, hb]
    have hpoint : rootPoint (x.hom ≫ U.inclusion) S a = w ≫ U.inclusion.hom.hom := by
      change (rootPoint x.hom S a) ≫ U.inclusion.hom.hom = _
      exact congrArg (· ≫ U.inclusion.hom.hom) ha
    rw [hbase, hpoint] at he
    simpa only [q, w, z, Category.assoc] using he

/-- Conditional derivation of the scheme centre from ordered root products. -/
theorem schemeCentre_conditional.{v}
    (_borel : BorelRadicalProduct.{v})
    (contract : ContractingProduct.{v})
    (cell : RegularRootCell.{v}) : Specs.SchemeCentre.CentreFormula.{v} := by
  intro k _ G hG T hT hmax
  obtain ⟨hFG, e, he⟩ := split_character_presentation hT
  refine ⟨hFG, e, he, ?_⟩
  let N := rootLattice T
  let q := diagonalClosedInclusion k N
  haveI : IsClosedImmersion q.hom.hom.left :=
    (LinearAlgebraicGroups.hopfMapClosedImmersion k _).mpr
      (groupAlgebraMap_surjective _ QuotientGroup.mk_surjective)
  haveI := T.isClosedImmersion
  let forget : GroupScheme k ⥤ Scheme :=
    Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  haveI : IsIso e.hom.hom.hom.left := inferInstanceAs (IsIso (forget.map e.hom))
  have h : IsClosedImmersion (q ≫ e.hom ≫ T.inclusion).hom.hom.left := by
    change IsClosedImmersion (q.hom.hom.left ≫ e.hom.hom.hom.left ≫ T.inclusion.hom.hom.left)
    infer_instance
  let Z : ClosedSubgroup G.val := ⟨_, q ≫ e.hom ≫ T.inclusion, h⟩
  have hpoints (R : TestAlgebra k) (t : GroupPoints T.group R) :
      Centralizes (𝟙 G.val) (t ≫ T.inclusion.hom.hom) ↔
        ∀ α ∈ absoluteRoots T, t ≫ α.hom.hom = 1 := by
    rw [central_torus_points contract cell hG hT hmax]
    exact forall_congr' fun α => forall_congr' fun _ => (torus_equations e he R t α).symm
  refine ⟨h, ?_, hpoints⟩
  obtain ⟨C, hC⟩ := LinearAlgebraicGroups.centralizerScheme k G
    ⟨G.val, 𝟙 _, inferInstanceAs (IsClosedImmersion (𝟙 G.val.X.left))⟩
  have hCi : Centralizes (𝟙 G.val) C.inclusion.hom.hom :=
    (hC _ _).mpr ⟨𝟙 _, Category.id_comp _⟩
  have hCT := LinearAlgebraicGroups.Reductive.TorusCentralizer.maximalTorusCentralizer
    G hG T (isTorus_of_split hT) hmax
  obtain ⟨t, ht⟩ := (hCT _ _).mp (centralizes_torus_of_central (T := T) hCi)
  haveI := G.property.1
  haveI := C.isClosedImmersion
  obtain ⟨A, ⟨a⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr
    (isAffine_of_isAffineHom C.inclusion.hom.hom.left)
  have ha : Centralizes (𝟙 G.val) ((a.hom ≫ t) ≫ T.inclusion.hom.hom) := by
    rw [Category.assoc, ht]
    exact centralizes_precomp hCi a.hom
  obtain ⟨z, hz⟩ := (diagonal_root_kernel e he A.unop _).mp ((hpoints A.unop _).mp ha)
  have hZ : Centralizes (𝟙 G.val) Z.inclusion.hom.hom := by
    let R := CommAlgCat.of k (MonoidAlgebra k (Character T.group ⧸ N))
    let tZ : GroupPoints T.group R := (q ≫ e.hom).hom.hom
    have hr := (diagonal_root_kernel e he R tZ).mpr ⟨𝟙 _, Category.id_comp _⟩
    exact (hpoints R tZ).mpr hr
  intro X g
  constructor
  · intro hg
    obtain ⟨c, hc⟩ := (hC X g).mp hg
    let zA : (testSpec k).obj A ⟶ Z.group.X := z
    have hzA : zA ≫ (q ≫ e.hom).hom.hom = a.hom ≫ t := hz
    refine ⟨c ≫ a.inv ≫ zA, ?_⟩
    change (c ≫ a.inv ≫ zA) ≫ ((q ≫ e.hom).hom.hom ≫ T.inclusion.hom.hom) = g
    simp only [Category.assoc, reassoc_of% hzA, Iso.inv_hom_id_assoc, ht, hc]
  · rintro ⟨s, rfl⟩
    exact centralizes_precomp hZ s

end

end LinearAlgebraicGroups.RootData.SchemeCentre

universe v8_closure_cf5b1151e8673056_u0
theorem _root_.«LinearAlgebraicGroups».«RootData».«SchemeCentre».«schemeCentre» : _root_.«LinearAlgebraicGroups».«Specs».«SchemeCentre».«CentreFormula».{v8_closure_cf5b1151e8673056_u0} :=
  @_root_.«LinearAlgebraicGroups».«RootData».«SchemeCentre».«schemeCentre_conditional».{v8_closure_cf5b1151e8673056_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«OrderedRootProducts».«borelRadicalProduct».{v8_closure_cf5b1151e8673056_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«OrderedRootProducts».«contractingProduct».{v8_closure_cf5b1151e8673056_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«OrderedRootProducts».«regularRootCell».{v8_closure_cf5b1151e8673056_u0})
