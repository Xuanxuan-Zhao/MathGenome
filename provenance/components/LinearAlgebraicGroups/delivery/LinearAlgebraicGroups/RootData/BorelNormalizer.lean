import Specs.LinearAlgebraicGroups.RootData.BorelNormalizer
import LinearAlgebraicGroups.RootData.RankOneFlag
import LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
import LinearAlgebraicGroups.Reductive.MaximalToriConjugate
import LinearAlgebraicGroups.Reductive.CocharacterDynamics
import LinearAlgebraicGroups.Reductive.BorelProper
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Order.BigOperators.Group.Finset

import LinearAlgebraicGroups.RootData.BorelsAndChambers
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.RootData.BorelNormalizer

open _root_.LinearAlgebraicGroups.Specs
open Specs.AbstractPairing (Root)
open Specs.BorelsAndChambers
open Specs.BorelNormalizer
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (absoluteRoots adjointWeightVectors characterValue pairing)
open Specs.GeometricBorelConjugacy (ConjugatesSubgroups IsBorel IsKBorel subgroupOfSubgroup)
open Specs.GeometricRadicals (IsMaximalTorus IsReductive IsSplitTorus IsTorus GeometricGroup
  baseChangedSubgroup)
open Specs.RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

open private conjugateLe_iff centralizes_iff mono_over comp_conjugateFamily
  from LinearAlgebraicGroups.Affine.Stabilizers
open private conjugates_trans conjugates_preserves_borel normalizes_of_conjugates_self
  conjugate conjugationIso comp_conjugate conjugate_inv_cancel
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private extendedGroupIso factor_of_baseChange
  from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private baseChangeMapIsPullback from LinearAlgebraicGroups.Flag.HomogeneousQuotient
open private isTorus_iff_coordinates restrictSubgroup compose_restrict local_maximal_of_ambient
  solvable_maximal_torus_iff maximal_of_square transportSubgroup
  conjugates_transport conjugates_in_ambient solvable_tori_conjugate
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private split_of_torus torus_of_split from LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private torus_baseChange_algClosure from LinearAlgebraicGroups.Reductive.SubtorusCentralizer
open private splitTorus_sectionsCommute from LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
open private factor_group_through_subgroup subgroupOf_mutual_iso
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private borel_transport from LinearAlgebraicGroups.Reductive.BorelProper
open private solvable_iff_sections from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private smooth_of_smooth_after_fieldExtension from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private tangent_image_iff laurentParameter_zpow monomial_coeff
  from LinearAlgebraicGroups.Reductive.CocharacterLieWeights
open private charactersOfIso cocharactersOfIso from LinearAlgebraicGroups.RootData.CharacterPairing
open private scalarExtendedPoint_natural constant_sections_after_scalar_extension
  from LinearAlgebraicGroups.RootData.RankOneFlag
open private baseChangeKernelSquare from LinearAlgebraicGroups.Affine.Components
open private closedImmersion_over_affineSpec quotientProjection factorsThrough_affineQuotient
  from LinearAlgebraicGroups.Affine.FixedPointSchemes
open private polynomialConstants polynomialConstants_laurent polynomialConstants_zero
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private multiply_isOpenImmersion from LinearAlgebraicGroups.Reductive.CocharacterOpenCell
open private sectionOfClosedPoint sectionOfClosedPoint_apply
  from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open LinearAlgebraicGroups.CocharacterDynamics
open Specs.AdjointRepresentation (GroupPoints RelativeTangent constants dualMap scale)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

variable {k : Type u} [Field k] {G : GroupScheme k}

-- Use the morphism equation for `SchemeDerivedGroup.FactorsThrough`.
private abbrev FactorsThrough (B : ClosedSubgroup G) {Y : SchemeOver k} (g : Y ⟶ G.X) : Prop :=
  ∃ b : Y ⟶ B.group.X, b ≫ B.inclusion.hom.hom = g

private abbrev extendSubgroup (K : Type u) [Field K] [Algebra k K]
    (B : ClosedSubgroup G) : ClosedSubgroup ((groupBaseChange k K).obj G) :=
  baseChangedSubgroup K B (baseChangeClosedSubgroup k K B.inclusion B.isClosedImmersion)

private theorem subgroup_extend (K : Type u) [Field K] [Algebra k K]
    {B C : ClosedSubgroup G} (h : IsSubgroupOf B C) :
    IsSubgroupOf (extendSubgroup K B) (extendSubgroup K C) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨(groupBaseChange k K).map f, by
    change (groupBaseChange k K).map f ≫ (groupBaseChange k K).map C.inclusion = _
    rw [← Functor.map_comp, hf]
    rfl⟩

private theorem subgroup_descend (K : Type u) [Field K] [Algebra k K]
    {B C : ClosedSubgroup G} (h : IsSubgroupOf (extendSubgroup K B) (extendSubgroup K C)) :
    IsSubgroupOf B C := by
  obtain ⟨q, hq⟩ := h
  letI := C.isClosedImmersion
  obtain ⟨b, hb⟩ := factor_of_baseChange K B.inclusion.hom.hom C.inclusion.hom.hom
    q.hom.hom (congrArg (fun f : (extendSubgroup K B).group ⟶
      (groupBaseChange k K).obj G ↦ f.hom.hom) hq)
  exact factor_group_through_subgroup C B.inclusion b hb

private abbrev standardTorus (k : Type u) [Field k] (n : ℕ) : GroupScheme k :=
  (StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin n))).val

private def standardTorusExtension (K : Type u) [Field K] [Algebra k K] (n : ℕ) :
    (groupBaseChange k K).obj (standardTorus k n) ≅ standardTorus K n := by
  classical
  let M := Specs.CharacterDescent.StandardLattice.{u} n
  let A := Specs.DiagonalizableGroups.groupAlgebra k M
  let B := Specs.DiagonalizableGroups.groupAlgebra K M
  let e := (LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) n).some
  let f := (LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := K) n).some
  let a : extendedHopf K A ≅ B := CommHopfAlgCat.isoMk
    (LinearAlgebraicGroups.CharacterDescent.groupAlgebraBaseChange k K M)
  exact (groupBaseChange k K).mapIso e.symm ≪≫ (extendedGroupIso K A).symm ≪≫
    (hopfSpec (CommRingCat.of K)).mapIso a.op.symm ≪≫ f

private theorem fieldSpecMap_isIso [IsAlgClosed k] :
    IsIso (fieldSpecMap k (AlgebraicClosure k)) := by
  let f := CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))
  letI : IsIso f := (ConcreteCategory.isIso_iff_bijective f).mpr
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  change IsIso (Spec.map f)
  infer_instance

private theorem groupObjectsFunctor_isEquivalence {C D : Type*} [Category* C] [Category* D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
    (F : C ⥤ D) [hF : F.Monoidal] [F.IsEquivalence] : F.mapGrp.IsEquivalence := by
  letI : F.asEquivalence.functor.Monoidal := hF
  letI : F.asEquivalence.inverse.Monoidal := Functor.Monoidal.ofChosenFiniteProducts _
  exact F.asEquivalence.mapGrp.isEquivalence_functor

private theorem groupBaseChange_isEquivalence [IsAlgClosed k] :
    (groupBaseChange k (AlgebraicClosure k)).IsEquivalence := by
  let b := fieldSpecMap k (AlgebraicClosure k)
  letI : IsIso b := fieldSpecMap_isIso
  letI : (Over.pullback b).IsEquivalence :=
    (Over.mapPullbackAdj b).isEquivalence_right_of_isEquivalence_left
  exact groupObjectsFunctor_isEquivalence (Over.pullback b)

private theorem closedImmersion_of_extend_iso (K : Type u) [Field K] [Algebra k K]
    [IsIso (fieldSpecMap k K)] {X Y : SchemeOver k} (f : X ⟶ Y)
    (hf : IsClosedImmersion ((baseChange k K).map f).left) : IsClosedImmersion f.left := by
  let b := fieldSpecMap k K
  have h := (baseChangeMapIsPullback K f).w
  have h' : IsClosedImmersion (((baseChange k K).map f).left ≫ pullback.fst Y.hom b) :=
    IsClosedImmersion.comp _ _
  rw [h] at h'
  exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
    (pullback.fst X.hom b) f.left).mp h'

private theorem pullback_subgroup_over_closed_field [IsAlgClosed k] (A : AffineAlgebraicGroup k)
    (B : ClosedSubgroup (GeometricGroup A).val) :
    ∃ C : ClosedSubgroup A.val, ∃ e : (extendSubgroup (AlgebraicClosure k) C).group ≅ B.group,
      e.hom ≫ B.inclusion = (extendSubgroup (AlgebraicClosure k) C).inclusion := by
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  letI : IsIso (fieldSpecMap k K) := fieldSpecMap_isIso
  letI : F.IsEquivalence := groupBaseChange_isEquivalence
  let I := F.asEquivalence.inverse.obj B.group
  let e : F.obj I ≅ B.group := F.asEquivalence.counitIso.app B.group
  let i : I ⟶ A.val := F.preimage (e.hom ≫ B.inclusion)
  have hi : F.map i = e.hom ≫ B.inclusion := F.map_preimage _
  have hc : IsClosedImmersion i.hom.hom.left := by
    apply closedImmersion_of_extend_iso K
    change IsClosedImmersion (F.map i).hom.hom.left
    rw [hi]
    letI := B.isClosedImmersion
    letI : IsIso e.hom.hom.hom.left := (Grp.forget _ ⋙ Over.forget _).map_isIso e.hom
    exact IsClosedImmersion.comp _ _
  exact ⟨⟨I, i, hc⟩, e, hi.symm⟩

private theorem same_of_inclusion_iso {B C : ClosedSubgroup G}
    (e : B.group ≅ C.group) (he : e.hom ≫ C.inclusion = B.inclusion) : SameSubgroup B C :=
  ⟨⟨e.hom, he⟩, ⟨e.inv, by rw [← he, e.inv_hom_id_assoc]⟩⟩

private theorem geometricMaximal_of_maximal [IsAlgClosed k] (A : AffineAlgebraicGroup k)
    (T : ClosedSubgroup A.val) (hT : IsMaximalTorus T) : IsGeometricallyMaximal T := by
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  letI : IsIso (fieldSpecMap k K) := fieldSpecMap_isIso
  letI : F.IsEquivalence := groupBaseChange_isEquivalence
  let T' := extendSubgroup K T
  refine ⟨T'.isClosedImmersion, torus_baseChange_algClosure (closedSubgroupAlgebraicGroup T) hT.1, ?_⟩
  intro U hU hTU
  obtain ⟨S, e, he⟩ := pullback_subgroup_over_closed_field A U
  have hSame := same_of_inclusion_iso e he
  obtain ⟨r, ⟨q⟩⟩ := split_of_torus (D := closedSubgroupAlgebraicGroup (G := GeometricGroup A) U)
    ((isTorus_iff_coordinates _).mp hU)
  have hS : IsTorus S.group := by
    apply (isTorus_iff_coordinates (closedSubgroupAlgebraicGroup S)).mpr
    apply torus_of_split
    let c : F.obj S.group ≅ F.obj (standardTorus k r) := e ≪≫ q ≪≫ (standardTorusExtension K r).symm
    exact ⟨r, ⟨(Functor.FullyFaithful.ofFullyFaithful F).preimageIso c⟩⟩
  obtain ⟨a, ha⟩ := hTU
  obtain ⟨b, hb⟩ := hSame.2
  obtain ⟨d, hd⟩ := hT.2 S hS (subgroup_descend K
    (B := T) (C := S) ⟨a ≫ b, by rw [Category.assoc, hb, ha]⟩)
  obtain ⟨l, hl⟩ := subgroup_extend K (B := S) (C := T) ⟨d, hd⟩
  exact ⟨b ≫ l, by rw [Category.assoc, hl, hb]⟩

private theorem avoids_finite_kernels {V I : Type u} [AddCommGroup V]
    (s : Finset I) (f : I → V →ₗ[ℤ] ℤ) (hf : ∀ i, f i ≠ 0) :
    ∃ v : V, ∀ i ∈ s, f i v ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi hs =>
    obtain ⟨v, hv⟩ := hs
    by_cases hvi : f i v = 0
    · obtain ⟨w, hw⟩ : ∃ w, f i w ≠ 0 := by
        by_contra! hn
        exact hf i (LinearMap.ext hn)
      let bad : Finset ℤ := s.image (fun j ↦ -(f j v) / f j w)
      obtain ⟨n, hn⟩ := (insert 0 bad).exists_notMem
      have hn0 : n ≠ 0 := fun h ↦ hn (h ▸ Finset.mem_insert_self _ _)
      refine ⟨v + n • w, ?_⟩
      intro j hj hj0
      simp only [map_add, map_zsmul, Int.zsmul_eq_mul] at hj0
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (mul_ne_zero hn0 hw) (by simpa [hvi] using hj0)
      · have hfw : f j w ≠ 0 := by
          intro he
          exact hv j hj (by simpa [he] using hj0)
        have hn' : n = -(f j v) / f j w := by
          have he : -(f j v) = n * f j w := by linarith
          rw [he, Int.mul_ediv_cancel _ hfw]
        exact hn (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hj, hn'.symm⟩))
    · exact ⟨v, fun j hj ↦ (Finset.mem_insert.mp hj).elim
        (fun h ↦ h ▸ hvi) (hv j)⟩

private theorem exists_regular_cocharacter (A : AffineAlgebraicGroup k)
    (T : ClosedSubgroup A.val) (hT : IsSplitTorus T.group) :
    ∃ cochar : Cocharacter T.group, IsRegular T cochar := by
  classical
  obtain ⟨hc, _, _, _, _, P, hP, hpair⟩ :=
    LinearAlgebraicGroups.RootData.CharacterPairing.perfectCharacterPairing T.group hT
  letI := hc
  letI := hP
  letI : Finite (Root T) :=
    (LinearAlgebraicGroups.RootData.CharacterPairing.finiteAbsoluteRoots A T hT).to_subtype
  letI := Fintype.ofFinite (Root T)
  let f (α : Root T) := P (Additive.ofMul α.val)
  have hf (α : Root T) : f α ≠ 0 := by
    intro h
    have h' : (Additive.ofMul α.val : Additive (Character T.group)) = 0 :=
      P.toPerfPair.injective (show P (Additive.ofMul α.val) = P 0 by simpa [f] using h)
    exact α.property.1 (show α.val = 1 from h')
  obtain ⟨v, hv⟩ := avoids_finite_kernels Finset.univ f hf
  refine ⟨v.toMul, fun α ↦ ?_⟩
  have hh := hv α (Finset.mem_univ α)
  change P (Additive.ofMul α.val) (Additive.ofMul v.toMul) ≠ 0 at hh
  rwa [hpair] at hh

private theorem normalizes_iff_sections (B : ClosedSubgroup G) {Y : SchemeOver k}
    (g : Y ⟶ G.X) :
    Normalizes B.inclusion g ↔
      ∀ (Z : SchemeOver k) (z : Z ⟶ Y) (b : Z ⟶ B.group.X),
        FactorsThrough B ((z ≫ g) * (b ≫ B.inclusion.hom.hom) * (z ≫ g)⁻¹) ∧
        FactorsThrough B ((z ≫ g)⁻¹ * (b ≫ B.inclusion.hom.hom) * (z ≫ g)) := by
  rw [normalizesIff k _ B.isClosedImmersion, conjugateLe_iff, conjugateLe_iff]
  simp only [GrpObj.comp_inv, inv_inv, ← forall_and]

private theorem subgroup_normalizes (B : ClosedSubgroup G) {Y : SchemeOver k} {g : Y ⟶ G.X}
    (hg : FactorsThrough B g) : Normalizes B.inclusion g := by
  obtain ⟨b, hb⟩ := hg
  rw [← hb, normalizes_iff_sections]
  intro Z z c
  exact ⟨⟨(z ≫ b) * c * (z ≫ b)⁻¹, by
      simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]⟩,
    ⟨(z ≫ b)⁻¹ * c * (z ≫ b), by
      simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]⟩⟩

private theorem normalizes_mul (B : ClosedSubgroup G) {Y : SchemeOver k} {g h : Y ⟶ G.X}
    (hg : Normalizes B.inclusion g) (hh : Normalizes B.inclusion h) :
    Normalizes B.inclusion (g * h) := by
  rw [normalizes_iff_sections] at hg hh ⊢
  intro Z z b
  obtain ⟨c, hc⟩ := (hh Z z b).1
  obtain ⟨d, hd⟩ := (hg Z z b).2
  refine ⟨?_, ?_⟩
  · have := (hg Z z c).1
    rw [hc] at this
    convert this using 1
    simp only [MonObj.comp_mul, mul_inv_rev]
    group
  · have := (hh Z z d).2
    rw [hd] at this
    convert this using 1
    simp only [MonObj.comp_mul, mul_inv_rev]
    group

private theorem normalizes_inv (B : ClosedSubgroup G) {Y : SchemeOver k} {g : Y ⟶ G.X}
    (hg : Normalizes B.inclusion g) : Normalizes B.inclusion g⁻¹ := by
  rw [normalizes_iff_sections] at hg ⊢
  simpa only [GrpObj.comp_inv, inv_inv, and_comm] using hg

private theorem conjugates_of_normalizes (B : ClosedSubgroup G)
    {g : 𝟙_ (SchemeOver k) ⟶ G.X} (hg : Normalizes B.inclusion g) :
    ConjugatesSubgroups g B B := by
  let I := conjugationIso g
  let J := conjugationIso g⁻¹
  obtain ⟨f, hf⟩ := ((normalizes_iff_sections B g).mp hg
    B.group.X (toUnit _) (𝟙 _)).1
  obtain ⟨r, hr⟩ := ((normalizes_iff_sections B g).mp hg
    B.group.X (toUnit _) (𝟙 _)).2
  rw [Category.id_comp] at hf hr
  have hn (x : B.group.X ⟶ G.X) :
      x ≫ I.hom.hom.hom = (toUnit B.group.X ≫ g) * x * (toUnit B.group.X ≫ g)⁻¹ := by
    rw [show I.hom.hom.hom = conjugate g
      (𝟙 G.X) from rfl, comp_conjugate, Category.comp_id]
    rfl
  have hn' (x : B.group.X ⟶ G.X) :
      x ≫ J.hom.hom.hom = (toUnit B.group.X ≫ g)⁻¹ * x * (toUnit B.group.X ≫ g) := by
    rw [show J.hom.hom.hom = conjugate g⁻¹
      (𝟙 G.X) from rfl, comp_conjugate, Category.comp_id]
    simp only [conjugate, GrpObj.comp_inv, inv_inv]
  obtain ⟨a, ha⟩ := factor_group_through_subgroup B
    (B.inclusion ≫ I.hom) f (hf.trans (hn _).symm)
  obtain ⟨b, hb⟩ := factor_group_through_subgroup B
    (B.inclusion ≫ J.hom) r (hr.trans (hn' _).symm)
  haveI : Mono B.inclusion.hom.hom := mono_over _ B.isClosedImmersion
  have ha' : (a ≫ B.inclusion).hom.hom =
      (toUnit B.group.X ≫ g) * B.inclusion.hom.hom * (toUnit B.group.X ≫ g)⁻¹ :=
    (congrArg (fun m : B.group ⟶ G ↦ m.hom.hom) ha).trans (hn _)
  have hb' : (b ≫ B.inclusion).hom.hom =
      (toUnit B.group.X ≫ g)⁻¹ * B.inclusion.hom.hom * (toUnit B.group.X ≫ g) :=
    (congrArg (fun m : B.group ⟶ G ↦ m.hom.hom) hb).trans (hn' _)
  refine ⟨⟨a, b, ?_, ?_⟩, ha'⟩
  · apply Grp.hom_ext
    apply (cancel_mono B.inclusion.hom.hom).mp
    change a.hom.hom ≫ (b ≫ B.inclusion).hom.hom = B.inclusion.hom.hom
    rw [hb', MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv]
    simp only [← Category.assoc, comp_toUnit]
    change _ * (a ≫ B.inclusion).hom.hom * _ = _
    rw [ha']
    group
  · apply Grp.hom_ext
    apply (cancel_mono B.inclusion.hom.hom).mp
    change b.hom.hom ≫ (a ≫ B.inclusion).hom.hom = B.inclusion.hom.hom
    rw [ha', MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv]
    simp only [← Category.assoc, comp_toUnit]
    change _ * (b ≫ B.inclusion).hom.hom * _ = _
    rw [hb']
    group

private theorem conjugation_inverse {H I : GroupScheme k} {i : H ⟶ G} {j : I ⟶ G}
    {g : 𝟙_ (SchemeOver k) ⟶ G.X} {e : H ≅ I}
    (he : (e.hom ≫ j).hom.hom = conjugate g i.hom.hom) :
    (e.inv ≫ i).hom.hom = conjugate g⁻¹ j.hom.hom := by
  have he' : e.inv.hom.hom ≫ conjugate g i.hom.hom = j.hom.hom := by
    rw [← he]
    change (e.inv ≫ e.hom ≫ j).hom.hom = _
    rw [e.inv_hom_id_assoc]
  rw [← he', comp_conjugate, conjugate_inv_cancel]
  rfl

private theorem conjugates_inverse {B C : ClosedSubgroup G}
    {g : 𝟙_ (SchemeOver k) ⟶ G.X} (h : ConjugatesSubgroups g B C) :
    ConjugatesSubgroups g⁻¹ C B := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, conjugation_inverse he⟩

private theorem conjugates_same_target {B C D : ClosedSubgroup G}
    {g : 𝟙_ (SchemeOver k) ⟶ G.X} (hC : ConjugatesSubgroups g B C)
    (hD : ConjugatesSubgroups g B D) : SameSubgroup C D := by
  obtain ⟨e, he⟩ := hC
  obtain ⟨f, hf⟩ := hD
  have hh : f.hom ≫ D.inclusion = e.hom ≫ C.inclusion := Grp.hom_ext _ _ (hf.trans he.symm)
  exact ⟨⟨e.inv ≫ f.hom, by rw [Category.assoc, hh, e.inv_hom_id_assoc]⟩,
    ⟨f.inv ≫ e.hom, by rw [Category.assoc, ← hh, f.inv_hom_id_assoc]⟩⟩

private theorem conjugates_of_same {A B C : ClosedSubgroup G}
    {g : 𝟙_ (SchemeOver k) ⟶ G.X} (h : ConjugatesSubgroups g A B)
    (hs : SameSubgroup B C) : ConjugatesSubgroups g A C := by
  obtain ⟨e, he⟩ := h
  obtain ⟨f, hf⟩ := subgroupOf_mutual_iso hs.1 hs.2
  exact ⟨e ≪≫ f, by simpa only [Iso.trans_hom, Category.assoc, hf] using he⟩

private theorem conjugation_coset (T B C : ClosedSubgroup G)
    (hTB : IsSubgroupOf T B)
    (hstab : ∀ n : 𝟙_ (SchemeOver k) ⟶ G.X, Normalizes T.inclusion n →
      ConjugatesSubgroups n B B → FactorsThrough T n)
    {g g' : 𝟙_ (SchemeOver k) ⟶ G.X} (hgT : Normalizes T.inclusion g)
    (hg : ConjugatesSubgroups g B C) (hg'T : Normalizes T.inclusion g') :
    ConjugatesSubgroups g' B C ↔ FactorsThrough T (g⁻¹ * g') := by
  constructor
  · intro hg'
    exact hstab _ (normalizes_mul T (normalizes_inv T hgT) hg'T)
      (conjugates_trans hg' (conjugates_inverse hg))
  · rintro ⟨t, ht⟩
    obtain ⟨j, hj⟩ := hTB
    have ht' : (t ≫ j.hom.hom) ≫ B.inclusion.hom.hom = g⁻¹ * g' := by
      change t ≫ (j ≫ B.inclusion).hom.hom = _
      rw [hj, ht]
    have hb := conjugates_preserves_borel B (t ≫ j.hom.hom)
    rw [ht'] at hb
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using conjugates_trans hb hg

private theorem subgroup_trans {A B C : ClosedSubgroup G} (hAB : IsSubgroupOf A B)
    (hBC : IsSubgroupOf B C) : IsSubgroupOf A C := by
  obtain ⟨a, ha⟩ := hAB
  obtain ⟨b, hb⟩ := hBC
  exact ⟨a ≫ b, by rw [Category.assoc, hb, ha]⟩

private theorem factor_trans {X : SchemeOver k} {x : X ⟶ G.X} {B C : ClosedSubgroup G}
    (hx : FactorsThrough B x) (h : IsSubgroupOf B C) : FactorsThrough C x := by
  obtain ⟨b, hb⟩ := hx
  obtain ⟨j, hj⟩ := h
  exact ⟨b ≫ j.hom.hom, by
    change b ≫ (j ≫ C.inclusion).hom.hom = x
    rw [hj, hb]⟩

private theorem split_of_maximal [IsAlgClosed k] {A : AffineAlgebraicGroup k}
    {T : ClosedSubgroup A.val} (hT : IsMaximalTorus T) : IsSplitTorus T.group :=
  split_of_torus (D := closedSubgroupAlgebraicGroup T) ((isTorus_iff_coordinates _).mp hT.1)

private theorem connected_of_reductive (A : AffineAlgebraicGroup k) (hA : IsReductive A) :
    ConnectedSpace A.val.X.left := by
  letI := hA.2.1
  exact GeometricallyConnected.connectedSpace_of_subsingleton A.val.X.hom

private theorem normalizing_centralizes_of_torus_quotient {T B : ClosedSubgroup G}
    (j : T.group ⟶ B.group) (hj : j ≫ B.inclusion = T.inclusion)
    {L : GroupScheme k} (q : B.group ⟶ L) [Mono (j ≫ q).hom.hom]
    (hcomm : ∀ Y : SchemeOver k, IsMulCommutative (Y ⟶ L.X))
    {X : SchemeOver k} {g : X ⟶ G.X} (hg : FactorsThrough B g)
    (hn : Normalizes T.inclusion g) : Centralizes T.inclusion g := by
  obtain ⟨b, rfl⟩ := hg
  haveI : Mono B.inclusion.hom.hom := mono_over _ B.isClosedImmersion
  have hj' : j.hom.hom ≫ B.inclusion.hom.hom = T.inclusion.hom.hom :=
    congrArg (fun f : T.group ⟶ G ↦ f.hom.hom) hj
  apply (centralizes_iff T.inclusion _).mpr
  intro Y y t
  obtain ⟨s, hs⟩ := ((normalizes_iff_sections T _).mp hn Y y t).1
  have he : s ≫ j.hom.hom = ((y ≫ b) * (t ≫ j.hom.hom)) * (y ≫ b)⁻¹ := by
    apply (cancel_mono B.inclusion.hom.hom).mp
    change s ≫ j.hom.hom ≫ B.inclusion.hom.hom = _ ≫ B.inclusion.hom.hom
    rw [hj', hs, MonObj.mul_comp, GrpObj.inv_comp, MonObj.mul_comp]
    simp only [Category.assoc, hj']
  have hst : s = t := by
    apply (cancel_mono (j ≫ q).hom.hom).mp
    change s ≫ (j.hom.hom ≫ q.hom.hom) = t ≫ (j.hom.hom ≫ q.hom.hom)
    rw [← Category.assoc, he, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
    letI := hcomm Y
    rw [mul_comm' ((y ≫ b) ≫ q.hom.hom), mul_assoc, mul_inv_cancel, mul_one, Category.assoc]
  rw [hst] at hs
  exact mul_inv_eq_iff_eq_mul.mp hs.symm

private theorem geom_borel_normalizer_torus [IsAlgClosed k] (A : AffineAlgebraicGroup k)
    (hA : IsReductive A) {T B : ClosedSubgroup A.val} (hT : IsMaximalTorus T)
    (hB : IsBorel B) (hTB : IsSubgroupOf T B) {X : SchemeOver k} {g : X ⟶ A.val.X}
    (hg : FactorsThrough B g) (hn : Normalizes T.inclusion g) : FactorsThrough T g := by
  obtain ⟨j, hj⟩ := hTB
  let S := restrictSubgroup T B j hj
  have hS := compose_restrict T B j hj
  let D := closedSubgroupAlgebraicGroup B
  have hmax : IsMaximalTorus S := local_maximal_of_ambient _ _ (hS.symm ▸ hT)
  obtain ⟨U, L, q, _, _, hL, _, hsplit⟩ :=
    LinearAlgebraicGroups.GeometricTorusSplitting.splitting D hB.1.1 hB.1.2.1 hB.1.2.2
  haveI : IsIso (j ≫ q) := (hsplit S).1.mp ((solvable_maximal_torus_iff D S).mpr hmax)
  haveI : IsIso (j ≫ q).hom.hom := (Grp.forget _).map_isIso (j ≫ q)
  have hcentral := normalizing_centralizes_of_torus_quotient j hj q
    (splitTorus_sectionsCommute hL) hg hn
  exact (LinearAlgebraicGroups.Reductive.TorusCentralizer.maximalTorusCentralizer A hA T
    hT.1 (geometricMaximal_of_maximal A T hT) X g).mp hcentral

/-- The scheme intersection of the torus normalizer and a Borel through it. -/
theorem borelNormalizerIntersection_conditional.{v}
    (_ : BorelsThroughT.{v}) (_ : GeometricBorelChamberConjugacy.{v})
    (_ : GeometricBorelRootSubgroups.{v}) (_ : PositiveSystemsFromCocharacters.{v})
    (_ : RegularCocharacterBorel.{v}) : BorelNormalizerIntersection.{v} := by
  intro k _ _ A hA T B hT hB hTB N hN Y y
  change FactorsThrough T y ↔ ∀ H ∈ ({N, B} : Set (ClosedSubgroup A.val)), FactorsThrough H y
  constructor
  · intro h H hH
    rcases Set.mem_insert_iff.mp hH with rfl | hH
    · exact (hN Y y).mp (subgroup_normalizes T h)
    · rw [Set.mem_singleton_iff.mp hH]
      exact factor_trans h hTB
  · intro h
    exact geom_borel_normalizer_torus A hA hT hB hTB (h B (by simp))
      ((hN Y y).mpr (h N (by simp)))

private theorem schemeBaseChange_isEquivalence (K : Type u) [Field K] [Algebra k K]
    [IsIso (fieldSpecMap k K)] : (baseChange k K).IsEquivalence := by
  exact (Over.mapPullbackAdj (fieldSpecMap k K)).isEquivalence_right_of_isEquivalence_left

open scoped CategoryTheory.Obj in
private def extendRationalEquiv (K : Type u) [Field K] [Algebra k K]
    [IsIso (fieldSpecMap k K)] (H : GroupScheme k) :
    (𝟙_ (SchemeOver k) ⟶ H.X) ≃* (𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj H).X) := by
  let F := baseChange k K
  letI : F.IsEquivalence := schemeBaseChange_isEquivalence K
  let e := (Functor.FullyFaithful.ofFullyFaithful F).homMulEquiv (X := 𝟙_ (SchemeOver k)) (M := H.X)
  let i := asIso (Functor.LaxMonoidal.ε F)
  refine e.trans { toFun := fun p ↦ i.hom ≫ p, invFun := fun p ↦ i.inv ≫ p
                   left_inv := ?_, right_inv := ?_, map_mul' := ?_ }
  · intro p
    change i.inv ≫ i.hom ≫ p = p
    exact i.inv_hom_id_assoc p
  · intro p
    change i.hom ≫ i.inv ≫ p = p
    exact i.hom_inv_id_assoc p
  · intro f g
    exact MonObj.comp_mul _ f g

private theorem smooth_extend_iff (K : Type u) [Field K] [Algebra k K] (X : SchemeOver k) :
    Smooth ((baseChange k K).obj X).hom ↔ Smooth X.hom :=
  ⟨fun h ↦ smooth_of_smooth_after_fieldExtension (K := K) X.hom h,
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback X.hom (fieldSpecMap k K))⟩

private theorem connected_extend_iso_iff (K : Type u) [Field K] [Algebra k K]
    [IsIso (fieldSpecMap k K)] (X : SchemeOver k) :
    ConnectedSpace ((baseChange k K).obj X).left ↔ ConnectedSpace X.left := by
  let p := pullback.fst X.hom (fieldSpecMap k K)
  exact p.homeomorph.connectedSpace_iff

private theorem smoothConnectedSolvable_of_iso
    (D : AffineAlgebraicGroup k) (E : AffineAlgebraicGroup k) [IsAlgClosed k]
    (e : D.val ≅ E.val)
    (h : Smooth D.val.X.hom ∧ ConnectedSpace D.val.X.left ∧ SchemeDerivedGroup.IsSolvable D.val) :
    Smooth E.val.X.hom ∧ ConnectedSpace E.val.X.left ∧ SchemeDerivedGroup.IsSolvable E.val := by
  let i := (Grp.forget (SchemeOver k) ⋙ Over.forget _).mapIso e
  have hs : Smooth E.val.X.hom :=
    (MorphismProperty.cancel_left_of_respectsIso @Smooth i.hom E.val.X.hom).mp
      ((Over.w e.hom.hom.hom).symm ▸ h.1)
  have hc : ConnectedSpace E.val.X.left := i.hom.homeomorph.connectedSpace_iff.mp h.2.1
  haveI : Group.IsSolvable (𝟙_ (SchemeOver k) ⟶ D.val.X) :=
    (solvable_iff_sections D h.1 h.2.1).mp h.2.2
  let a : (𝟙_ (SchemeOver k) ⟶ D.val.X) ≃* (𝟙_ (SchemeOver k) ⟶ E.val.X) :=
    ((yonedaGrp.mapIso e).app (Opposite.op (𝟙_ (SchemeOver k)))).groupIsoToMulEquiv
  exact ⟨hs, hc, (solvable_iff_sections E hs hc).mpr
    (Group.isSolvable_of_surjective (f := a.toMonoidHom) a.surjective)⟩

private theorem smoothConnectedSolvable_extend_iff [IsAlgClosed k] (D : AffineAlgebraicGroup k) :
    (Smooth (GeometricGroup D).val.X.hom ∧ ConnectedSpace (GeometricGroup D).val.X.left ∧
      SchemeDerivedGroup.IsSolvable (GeometricGroup D).val) ↔
    (Smooth D.val.X.hom ∧ ConnectedSpace D.val.X.left ∧ SchemeDerivedGroup.IsSolvable D.val) := by
  let K := AlgebraicClosure k
  letI : IsIso (fieldSpecMap k K) := fieldSpecMap_isIso
  let e := extendRationalEquiv K D.val
  constructor
  · rintro ⟨hs, hc, hv⟩
    have hs' := (smooth_extend_iff K D.val.X).mp hs
    have hc' := (connected_extend_iso_iff K D.val.X).mp hc
    haveI : Group.IsSolvable (𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj D.val).X) :=
      (solvable_iff_sections (GeometricGroup D) hs hc).mp hv
    exact ⟨hs', hc', (solvable_iff_sections D hs' hc').mpr
      (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)⟩
  · rintro ⟨hs, hc, hv⟩
    have hs' := (smooth_extend_iff K D.val.X).mpr hs
    have hc' := (connected_extend_iso_iff K D.val.X).mpr hc
    haveI : Group.IsSolvable (𝟙_ (SchemeOver k) ⟶ D.val.X) :=
      (solvable_iff_sections D hs hc).mp hv
    exact ⟨hs', hc', (solvable_iff_sections (GeometricGroup D) hs' hc').mpr
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)⟩

private theorem isKBorel_iff_of_isAlgClosed [IsAlgClosed k] (A : AffineAlgebraicGroup k)
    (B : ClosedSubgroup A.val) : IsKBorel B ↔ IsBorel B := by
  let K := AlgebraicClosure k
  let B' := extendSubgroup K B
  let eB := smoothConnectedSolvable_extend_iff (closedSubgroupAlgebraicGroup B)
  constructor
  · rintro ⟨_, hB : IsBorel B'⟩
    refine ⟨eB.mp hB.1, fun C hC hBC ↦ ?_⟩
    exact subgroup_descend K (hB.2 (extendSubgroup K C)
      ((smoothConnectedSolvable_extend_iff (closedSubgroupAlgebraicGroup C)).mpr hC)
      (subgroup_extend K hBC))
  · intro hB
    refine ⟨B'.isClosedImmersion, eB.mpr hB.1, ?_⟩
    intro C hC hBC
    obtain ⟨D, e, he⟩ := pullback_subgroup_over_closed_field A C
    let D' := extendSubgroup K D
    have hsame := same_of_inclusion_iso e he
    have hD' : GeometricBorelConjugacy.IsSmoothConnectedSolvable D' :=
      smoothConnectedSolvable_of_iso (closedSubgroupAlgebraicGroup (G := GeometricGroup A) C)
        (closedSubgroupAlgebraicGroup (G := GeometricGroup A) D') e.symm hC
    have hD := (smoothConnectedSolvable_extend_iff (closedSubgroupAlgebraicGroup D)).mp hD'
    have hDB := hB.2 D hD (subgroup_descend K (subgroup_trans hBC hsame.2))
    exact subgroup_trans hsame.2 (subgroup_extend K hDB)

private theorem lieImage_mono {B C : ClosedSubgroup G} (h : IsSubgroupOf B C) :
    lieImage B ⊆ lieImage C := by
  obtain ⟨j, hj⟩ := h
  rintro _ ⟨v, rfl⟩
  refine ⟨mapPointKernel j v, ?_⟩
  apply Subtype.ext
  change v.toMul.val ≫ j.hom.hom ≫ C.inclusion.hom.hom = v.toMul.val ≫ B.inclusion.hom.hom
  exact congrArg (fun f : B.group ⟶ G ↦ v.toMul.val ≫ f.hom.hom) hj

private theorem relativeLieImage_mono {B C : ClosedSubgroup G} (h : IsSubgroupOf B C)
    {R : TestAlgebra k} : relativeLieImage B R ⊆ relativeLieImage C R := by
  obtain ⟨j, hj⟩ := h
  intro v hv
  obtain ⟨q, hq⟩ := (tangent_image_iff B R v).mp hv
  apply (tangent_image_iff C R v).mpr
  refine ⟨q ≫ j.hom.hom, ?_⟩
  change (q ≫ j.hom.hom) ≫ C.inclusion.hom.hom = v.toMul.val
  rw [Category.assoc]
  exact (congrArg (fun f : B.group ⟶ G ↦ q ≫ f.hom.hom) hj).trans hq

/-- A Borel through a maximal torus contains every invariant tangent class. -/
theorem lieQuotientZeroWeight_conditional.{v}
    (correspondence : BorelsThroughT.{v}) (_ : GeometricBorelChamberConjugacy.{v})
    (_ : GeometricBorelRootSubgroups.{v}) (_ : PositiveSystemsFromCocharacters.{v})
    (_ : RegularCocharacterBorel.{v}) : LieQuotientZeroWeight.{v} := by
  intro k _ _ A hA T B hT hB hTB x hx
  obtain ⟨cochar, D, _, hsame, _⟩ := (correspondence A hA T (split_of_maximal hT)
    (geometricMaximal_of_maximal A T hT)).1 B ((isKBorel_iff_of_isAlgClosed A B).mpr hB) hTB
  let c := cochar ≫ T.inclusion
  let s := LinearAlgebraicGroups.identityLieStructure A
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨W, hP, _, _⟩ := lieWeights A c D s
  apply lieImage_mono hsame.2
  rw [hP]
  intro j hj
  let R₀ := CommAlgCat.of k k
  let R := laurentAlgebra R₀
  let t := laurentParameter R₀
  let a := laurentConstants R₀
  let v : ULift (Fin W.dimension) → R := fun i ↦ a.hom (W.basis.equivFun x i)
  let w : ULift (Fin W.dimension) → R := fun i ↦ (↑(t ^ W.weight i) : R) * v i
  have ha : a = CommAlgCat.ofHom (Algebra.ofId k R) := by ext
  have hp : (W.coordinates.equiv R v).toMul.val =
      mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))) x.toMul.val := by
    rw [← ha]
    exact (W.coordinates.naturality a (W.basis.equivFun x)).trans
      (congrArg (mapPoints (dualMap a)) (W.coordinates.at_base x))
  have hd := W.diagonal R t v
  have h := hx R (cocharacterPoint cochar R t)
  have hdisp : W.coordinates.equiv R (w - v) ∈ relativeLieImage B R := by
    obtain ⟨q, hq⟩ := h
    refine ⟨q, ?_⟩
    rw [map_sub]
    change q.toMul.val ≫ B.inclusion.hom.hom =
      (W.coordinates.equiv R w).toMul.val * (W.coordinates.equiv R v).toMul.val⁻¹
    rw [hd]
    let b : GroupPoints A.val (CommAlgCat.of k (DualNumber R)) :=
      mapPoints (constants R) (cocharacterPoint c R t)
    change q.toMul.val ≫ B.inclusion.hom.hom =
      b * (W.coordinates.equiv R v).toMul.val * b⁻¹ * (W.coordinates.equiv R v).toMul.val⁻¹
    rw [hp]
    exact hq
  have hz := ((relativeLieWeights A c D s W R (w - v)).1.mp
    (relativeLieImage_mono hsame.1 hdisp)) j hj
  have hz' : LaurentPolynomial.T (W.weight j) * LaurentPolynomial.C (W.basis.equivFun x j) =
      LaurentPolynomial.C (W.basis.equivFun x j) := by
    apply sub_eq_zero.mp
    change (w j - v j : LaurentPolynomial k) = 0 at hz
    rwa [show w j = LaurentPolynomial.T (W.weight j) * LaurentPolynomial.C (W.basis.equivFun x j) by
      dsimp only [w, v]
      rw [laurentParameter_zpow]
      rfl] at hz
  have hcoeff := congrArg (fun p : LaurentPolynomial k ↦ p.coeff (W.weight j)) hz'
  simpa only [monomial_coeff, eq_self, ite_true, LaurentPolynomial.C_apply,
    ne_of_lt hj, Ne.symm (ne_of_lt hj), ite_false] using hcoeff

private theorem conjugates_transport_ambient (B : ClosedSubgroup G)
    (g : 𝟙_ (SchemeOver k) ⟶ G.X) :
    ConjugatesSubgroups g B (transportSubgroup (conjugationIso g) B) := by
  refine ⟨Iso.refl _, ?_⟩
  change B.inclusion.hom.hom ≫ conjugate g (𝟙 G.X) = conjugate g B.inclusion.hom.hom
  rw [comp_conjugate, Category.comp_id]

private theorem conjugates_of_comp_ambient {B C : ClosedSubgroup G}
    {g : 𝟙_ (SchemeOver k) ⟶ G.X} {e : B.group ≅ C.group}
    (he : e.hom ≫ C.inclusion = B.inclusion ≫ (conjugationIso g).hom) :
    ConjugatesSubgroups g B C := by
  refine ⟨e, ?_⟩
  change (e.hom ≫ C.inclusion).hom.hom = conjugate g B.inclusion.hom.hom
  rw [he]
  change B.inclusion.hom.hom ≫ conjugate g (𝟙 G.X) = _
  rw [comp_conjugate, Category.comp_id]

private theorem subgroup_conjugate {S B C : ClosedSubgroup G} {g : 𝟙_ (SchemeOver k) ⟶ G.X}
    (hSB : IsSubgroupOf S B) (hS : ConjugatesSubgroups g S S)
    (h : ConjugatesSubgroups g B C) : IsSubgroupOf S C := by
  obtain ⟨j, hj⟩ := hSB
  obtain ⟨e, he⟩ := hS
  obtain ⟨d, hd⟩ := h
  have hc : j ≫ d.hom ≫ C.inclusion = e.hom ≫ S.inclusion := by
    apply Grp.hom_ext
    change j.hom.hom ≫ (d.hom ≫ C.inclusion).hom.hom = (e.hom ≫ S.inclusion).hom.hom
    change (d.hom ≫ C.inclusion).hom.hom = conjugate g B.inclusion.hom.hom at hd
    change (e.hom ≫ S.inclusion).hom.hom = conjugate g S.inclusion.hom.hom at he
    rw [hd, comp_conjugate, he]
    exact congrArg (conjugate g) (congrArg (fun f : S.group ⟶ G ↦ f.hom.hom) hj)
  exact ⟨e.inv ≫ j ≫ d.hom, by rw [Category.assoc, Category.assoc, hc, e.inv_hom_id_assoc]⟩

private theorem finite_conjugation_on_characters (A : AffineAlgebraicGroup k) (hA : IsReductive A)
    (T : ClosedSubgroup A.val) (hT : IsTorus T.group) (hs : IsSplitTorus T.group)
    (g : 𝟙_ (SchemeOver k) ⟶ A.val.X) (hg : Normalizes T.inclusion g) :
    ∃ (e : T.group ≅ T.group) (w : MulAut (Character T.group)) (m : ℕ),
      InducesTorusConjugation T g e ∧ (∀ χ, w χ = e.inv ≫ χ) ∧ 0 < m ∧ w ^ m = 1 := by
  obtain ⟨N, C, j, hj, Q, q, hN, hC, hji, hq, _, _, _, hsplit, _⟩ :=
    LinearAlgebraicGroups.NormalizerLatticeAction.quotientByCentralizer A hA.1
      (connected_of_reductive A hA) T hT
  obtain ⟨W⟩ := hsplit hs
  obtain ⟨n, hn⟩ := (hN _ g).mp hg
  let I : SchemeOver k := 𝟙_ (SchemeOver k)
  let a := n ≫ q.hom.hom
  let w := W.constantGroup.families I a (IsLocalRing.closedPoint k)
  have hw : a = toUnit I ≫ W.constantGroup.sectionPoint w := by
    apply (W.constantGroup.families I).injective
    rw [W.constantGroup.constant]
    apply LocallyConstant.ext
    intro x
    change W.constantGroup.families I a x = w
    have hx : x = IsLocalRing.closedPoint k := @Subsingleton.elim (PrimeSpectrum k) inferInstance _ _
    rw [hx]
  have h := W.conjugates I n w hw
  rw [hn] at h
  let l := lift (𝟙 T.group.X) (toUnit T.group.X)
  have h' := congrArg (l ≫ ·) h
  rw [comp_conjugateFamily] at h'
  dsimp only [I] at h'
  simp only [l, lift_fst_assoc, lift_snd_assoc, Category.id_comp] at h'
  haveI := W.finite
  refine ⟨W.conjugation w, w.val, orderOf w, h'.symm, W.characterAction w, orderOf_pos w, ?_⟩
  exact congrArg (fun a : W.labels ↦ a.val) (pow_orderOf_eq_one w)

private theorem pairing_precompose {H : GroupScheme k} (e : H ≅ H) (cochar : Cocharacter H)
    (χ : Character H) : pairing H χ (cochar ≫ e.inv) = pairing H (e.inv ≫ χ) cochar := by
  unfold pairing Specs.CharacterDescent.compositionPairing
  rw [Category.assoc]

/-- A finite-order torus automorphism preserving a regular sign pattern fixes a
regular integral cocharacter, obtained by summing the finite orbit. -/
private theorem invariant_regular_cocharacter {A : AffineAlgebraicGroup k}
    (T : ClosedSubgroup A.val) (hs : IsSplitTorus T.group)
    (e : T.group ≅ T.group) (w : MulAut (Character T.group)) (m : ℕ)
    (he : ∀ χ, w χ = e.inv ≫ χ) (hm : 0 < m) (hw : w ^ m = 1)
    (cochar : Cocharacter T.group) (hcochar : IsRegular T cochar)
    (hroots : Set.MapsTo w (CharacterPairing.absoluteRoots T) (CharacterPairing.absoluteRoots T))
    (hpos : ∀ α : Root T, 0 < pairing T.group (w α.val) cochar ↔ 0 < pairing T.group α.val cochar) :
    ∃ mu : Cocharacter T.group, IsRegular T mu ∧ mu ≫ e.hom = mu := by
  classical
  obtain ⟨hc, _, _, _, _, P, hP, hpair⟩ :=
    LinearAlgebraicGroups.RootData.CharacterPairing.perfectCharacterPairing T.group hs
  letI := hc
  letI := hP
  let L := (cocharactersOfIso e.symm).toAdditive.toIntLinearEquiv.toLinearMap
  let v := Additive.ofMul cochar
  have hstep (a : Additive (Cocharacter T.group)) (χ : Character T.group) :
      P (Additive.ofMul χ) (L a) = P (Additive.ofMul (w χ)) a := by
    change P (Additive.ofMul χ) (Additive.ofMul (a.toMul ≫ e.inv)) =
      P (Additive.ofMul (w χ)) (Additive.ofMul a.toMul)
    rw [hpair, hpair, he, pairing_precompose]
  have hp (n : ℕ) (χ : Character T.group) :
      P (Additive.ofMul χ) ((L ^ n) v) = pairing T.group ((w ^ n) χ) cochar := by
    induction n generalizing χ with
    | zero => simpa only [pow_zero, Module.End.one_apply, MulAut.one_apply, v] using hpair χ cochar
    | succ n ih =>
      rw [pow_succ' L, Module.End.mul_apply, hstep, ih, pow_succ w, MulAut.mul_apply]
  have hperiod : (L ^ m) v = v := by
    apply P.flip.toPerfPair.injective
    ext χ
    change P (Additive.ofMul χ.toMul) ((L ^ m) v) =
      P (Additive.ofMul χ.toMul) (Additive.ofMul cochar)
    rw [hp m χ.toMul, hw, MulAut.one_apply, hpair]
  let s := ∑ i ∈ Finset.range m, (L ^ i) v
  have hfix : L s = s := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    dsimp only [s]
    rw [map_sum]
    simp_rw [← Module.End.mul_apply, ← pow_succ']
    rw [Finset.sum_range_succ (f := fun i ↦ (L ^ (i + 1)) v),
      Finset.sum_range_succ' (f := fun i ↦ (L ^ i) v), hperiod, pow_zero, Module.End.one_apply]
  have hit (α : Root T) (i : ℕ) : ∃ β : Root T,
      β.val = (w ^ i) α.val ∧ (0 < pairing T.group β.val cochar ↔ 0 < pairing T.group α.val cochar) := by
    induction i with
    | zero => exact ⟨α, by simp, Iff.rfl⟩
    | succ i ih =>
      obtain ⟨β, hβ, hsign⟩ := ih
      exact ⟨⟨w β.val, hroots β.property⟩, by
        change w β.val = (w ^ (i + 1)) α.val
        rw [hβ, pow_succ', MulAut.mul_apply],
        (hpos β).trans hsign⟩
  refine ⟨s.toMul, ?_, ?_⟩
  · intro α
    have hsum : pairing T.group α.val s.toMul = ∑ i ∈ Finset.range m,
        pairing T.group ((w ^ i) α.val) cochar := by
      rw [← hpair]
      change P (Additive.ofMul α.val) (∑ i ∈ Finset.range m, (L ^ i) v) = _
      simp only [map_sum, hp]
    rw [hsum]
    have hn : (Finset.range m).Nonempty := ⟨0, Finset.mem_range.mpr hm⟩
    rcases lt_or_gt_of_ne (hcochar α) with hneg | hposα
    · apply ne_of_lt
      apply Finset.sum_neg (s := Finset.range m) _ hn
      intro i _
      obtain ⟨β, hβ, hb⟩ := hit α i
      rw [← hβ]
      exact lt_of_le_of_ne (le_of_not_gt (fun x ↦ (not_lt_of_gt hneg) (hb.mp x))) (hcochar β)
    · apply ne_of_gt
      apply Finset.sum_pos (s := Finset.range m) _ hn
      intro i _
      obtain ⟨β, hβ, hb⟩ := hit α i
      rw [← hβ]
      exact hb.mpr hposα
  · have hh : s.toMul ≫ e.inv = s.toMul := congrArg Additive.toMul hfix
    calc
      s.toMul ≫ e.hom = (s.toMul ≫ e.inv) ≫ e.hom := congrArg (· ≫ e.hom) hh.symm
      _ = s.toMul := by rw [Category.assoc, e.inv_hom_id, Category.comp_id]

open scoped CategoryTheory.Obj in
private theorem conjugates_extend (K : Type u) [Field K] [Algebra k K]
    {B C : ClosedSubgroup G} {g : 𝟙_ (SchemeOver k) ⟶ G.X}
    (h : ConjugatesSubgroups g B C) :
    ConjugatesSubgroups (scalarExtendedRationalPoint K g) (extendSubgroup K B) (extendSubgroup K C) := by
  obtain ⟨e, he⟩ := h
  let F := baseChange k K
  let E := groupBaseChange k K
  have hc : F.map (toUnit B.group.X ≫ g) = toUnit (F.obj B.group.X) ≫ scalarExtendedRationalPoint K g := by
    rw [Functor.map_comp, scalarExtendedRationalPoint, ← Category.assoc, Functor.Monoidal.toUnit_ε]
  refine ⟨E.mapIso e, ?_⟩
  change F.map e.hom.hom.hom ≫ F.map C.inclusion.hom.hom = _
  rw [← F.map_comp]
  change F.map (e.hom ≫ C.inclusion).hom.hom = _
  change (e.hom ≫ C.inclusion).hom.hom = (toUnit B.group.X ≫ g) * B.inclusion.hom.hom *
    (toUnit B.group.X ≫ g)⁻¹ at he
  rw [he, F.map_mul, F.map_mul, F.map_inv', hc]
  rfl

private theorem conjugates_descend (K : Type u) [Field K] [Algebra k K]
    {B C : ClosedSubgroup G} {g : 𝟙_ (SchemeOver k) ⟶ G.X}
    (h : ConjugatesSubgroups (scalarExtendedRationalPoint K g) (extendSubgroup K B) (extendSubgroup K C)) :
    ConjugatesSubgroups g B C := by
  let B' := transportSubgroup (conjugationIso g) B
  have hb : ConjugatesSubgroups g B B' := conjugates_transport_ambient B g
  have hh := conjugates_same_target (conjugates_extend K hb) h
  obtain ⟨e, he⟩ := subgroupOf_mutual_iso (subgroup_descend K hh.1) (subgroup_descend K hh.2)
  exact conjugates_of_comp_ambient he

private theorem isBorel_of_same {A : AffineAlgebraicGroup k} [IsAlgClosed k]
    {B C : ClosedSubgroup A.val} (h : SameSubgroup B C) (hB : IsBorel B) : IsBorel C := by
  obtain ⟨e, _⟩ := subgroupOf_mutual_iso h.1 h.2
  exact ⟨smoothConnectedSolvable_of_iso (closedSubgroupAlgebraicGroup B)
    (closedSubgroupAlgebraicGroup C) e hB.1,
    fun D hD hCD ↦ subgroup_trans (hB.2 D hD (subgroup_trans h.1 hCD)) h.1⟩

private theorem conjugate_isKBorel {A : AffineAlgebraicGroup k} (B : ClosedSubgroup A.val)
    (hB : IsKBorel B) (g : 𝟙_ (SchemeOver k) ⟶ A.val.X) :
    IsKBorel (transportSubgroup (conjugationIso g) B) := by
  let K := AlgebraicClosure k
  let C := transportSubgroup (conjugationIso g) B
  obtain ⟨_, hB' : IsBorel (extendSubgroup K B)⟩ := hB
  have h := conjugates_extend K (conjugates_transport_ambient B g)
  have hs := conjugates_same_target (conjugates_transport_ambient (extendSubgroup K B)
    (scalarExtendedRationalPoint K g)) h
  exact ⟨(extendSubgroup K C).isClosedImmersion,
    isBorel_of_same (A := GeometricGroup A) hs (borel_transport hB' (conjugationIso (scalarExtendedRationalPoint K g)))⟩

private def conjugateLie (g : 𝟙_ (SchemeOver k) ⟶ G.X) : Lie k G →+ Lie k G :=
  mapPointKernel (conjugationIso g).hom

private theorem conjugateLie_val (g : 𝟙_ (SchemeOver k) ⟶ G.X) (v : Lie k G) :
    (conjugateLie g v).toMul.val = conjugate g v.toMul.val := by
  change v.toMul.val ≫ conjugate g (𝟙 G.X) = _
  rw [comp_conjugate, Category.comp_id]

private theorem conjugateLie_inverse (g : 𝟙_ (SchemeOver k) ⟶ G.X) (v : Lie k G) :
    conjugateLie g⁻¹ (conjugateLie g v) = v := by
  apply Subtype.ext
  change (conjugateLie g⁻¹ (conjugateLie g v)).toMul.val = v.toMul.val
  rw [conjugateLie_val, conjugateLie_val, conjugate_inv_cancel]

private theorem mapPoints_conjugate {R S : TestAlgebra k} (a : R ⟶ S)
    (g : 𝟙_ (SchemeOver k) ⟶ G.X) (x : Points G.X R) :
    mapPoints a (conjugate g x) = conjugate g (mapPoints a x) :=
  comp_conjugate _ _ _

/-- The differential of conjugation transports a weight by inverse pullback. -/
private theorem conjugateLie_weight (T : ClosedSubgroup G)
    {g : 𝟙_ (SchemeOver k) ⟶ G.X} {e : T.group ≅ T.group}
    (he : InducesTorusConjugation T g e) {χ : Character T.group} {v : Lie k G}
    (hv : v ∈ adjointWeightVectors T χ) :
    conjugateLie g v ∈ adjointWeightVectors T (e.inv ≫ χ) := by
  intro R t
  let s : GroupPoints T.group R := t ≫ e.inv.hom.hom
  have ht : t ≫ T.inclusion.hom.hom = conjugate g (s ≫ T.inclusion.hom.hom) := by
    change (e.hom ≫ T.inclusion).hom.hom = conjugate g T.inclusion.hom.hom at he
    rw [← comp_conjugate, ← he]
    change t ≫ T.inclusion.hom.hom = t ≫ (e.inv ≫ e.hom ≫ T.inclusion).hom.hom
    rw [e.inv_hom_id_assoc]
  have hχ : characterValue (e.inv ≫ χ) R t = characterValue χ R s := by
    unfold characterValue
    simp only [s, Grp.comp_hom_hom, Category.assoc]
  let a := CommAlgCat.ofHom (Algebra.ofId k R)
  let x : GroupPoints G (CommAlgCat.of k (DualNumber R)) := mapPoints (dualMap a) v.toMul.val
  let y : GroupPoints G (CommAlgCat.of k (DualNumber R)) := mapPoints (constants R)
    (s ≫ T.inclusion.hom.hom)
  have hh : y * x * y⁻¹ = mapPoints (scale R (characterValue χ R s)) x := hv R s
  change mapPoints (constants R) (t ≫ T.inclusion.hom.hom) *
    mapPoints (dualMap a) (conjugateLie g v).toMul.val *
    (mapPoints (constants R) (t ≫ T.inclusion.hom.hom))⁻¹ =
      mapPoints (scale R (characterValue (e.inv ≫ χ) R t))
        (mapPoints (dualMap a) (conjugateLie g v).toMul.val)
  simp only [ht, hχ, conjugateLie_val, mapPoints_conjugate]
  change conjugate g y * conjugate g x * (conjugate g y)⁻¹ =
    conjugate g (mapPoints (scale R (characterValue χ R s)) x)
  rw [← hh]
  let c : GroupPoints G (CommAlgCat.of k (DualNumber R)) := toUnit _ ≫ g
  change (c * y * c⁻¹) * (c * x * c⁻¹) * (c * y * c⁻¹)⁻¹ = c * (y * x * y⁻¹) * c⁻¹
  group

private theorem conjugate_root_mem (T : ClosedSubgroup G)
    {g : 𝟙_ (SchemeOver k) ⟶ G.X} {e : T.group ≅ T.group}
    (he : InducesTorusConjugation T g e) :
    Set.MapsTo (fun χ ↦ e.inv ≫ χ) (absoluteRoots T) (absoluteRoots T) := by
  rintro χ ⟨hχ, v, hv, hv₀⟩
  change χ ≠ 1 at hχ
  refine ⟨?_, conjugateLie g v, conjugateLie_weight T he hv, ?_⟩
  · intro h
    exact hχ ((charactersOfIso e).injective (h.trans (map_one (charactersOfIso e)).symm))
  · intro h
    apply hv₀
    rw [← conjugateLie_inverse g v, h, map_zero]

private theorem conjugateLie_mem_lieImage {B C : ClosedSubgroup G}
    {g : 𝟙_ (SchemeOver k) ⟶ G.X} (hBC : ConjugatesSubgroups g B C)
    {v : Lie k G} (hv : v ∈ lieImage B) : conjugateLie g v ∈ lieImage C := by
  obtain ⟨e, he⟩ := hBC
  obtain ⟨x, rfl⟩ := hv
  refine ⟨mapPointKernel e.hom x, ?_⟩
  apply Subtype.ext
  change (x.toMul.val ≫ e.hom.hom.hom) ≫ C.inclusion.hom.hom =
    (conjugateLie g (mapPointKernel B.inclusion x)).toMul.val
  rw [conjugateLie_val, Category.assoc]
  change x.toMul.val ≫ (e.hom ≫ C.inclusion).hom.hom =
    conjugate g (x.toMul.val ≫ B.inclusion.hom.hom)
  rw [show (e.hom ≫ C.inclusion).hom.hom = conjugate g B.inclusion.hom.hom from he, comp_conjugate]

private theorem subgroupRoots_conjugate_subset (T : ClosedSubgroup G) {B C : ClosedSubgroup G}
    {g : 𝟙_ (SchemeOver k) ⟶ G.X} {e : T.group ≅ T.group}
    (he : InducesTorusConjugation T g e) (hBC : ConjugatesSubgroups g B C)
    (α : ↥(absoluteRoots T)) (hα : α ∈ subgroupRoots T B) :
    e.inv ≫ α.val ∈ Subtype.val '' subgroupRoots T C := by
  let β : ↥(absoluteRoots T) := ⟨e.inv ≫ α.val, conjugate_root_mem T he α.property⟩
  refine ⟨β, ?_, rfl⟩
  intro v hv
  have he' : InducesTorusConjugation T g⁻¹ e.symm := conjugation_inverse he
  have hχ : e.hom ≫ β.val = α.val := e.hom_inv_id_assoc _
  have hv' : conjugateLie g⁻¹ v ∈ adjointWeightVectors T α.val := by
    rw [← hχ]
    exact conjugateLie_weight T he' hv
  have h := conjugateLie_mem_lieImage hBC (hα hv')
  have hinv := conjugateLie_inverse g⁻¹ v
  rw [inv_inv] at hinv
  exact hinv ▸ h

private theorem subgroupRoots_conjugate_image (T : ClosedSubgroup G) {B C : ClosedSubgroup G}
    {g : 𝟙_ (SchemeOver k) ⟶ G.X} {e : T.group ≅ T.group}
    (he : InducesTorusConjugation T g e) (hBC : ConjugatesSubgroups g B C) :
    (fun χ : Character T.group ↦ e.inv ≫ χ) '' (Subtype.val '' subgroupRoots T B) =
      Subtype.val '' subgroupRoots T C := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨α, hα, rfl⟩, rfl⟩
    exact subgroupRoots_conjugate_subset T he hBC α hα
  · rintro _ ⟨β, hβ, rfl⟩
    have he' : InducesTorusConjugation T g⁻¹ e.symm := conjugation_inverse he
    obtain ⟨α, hα, hαval⟩ := subgroupRoots_conjugate_subset T he' (conjugates_inverse hBC) β hβ
    exact ⟨α.val, ⟨α, hα, rfl⟩, by
      change e.inv ≫ α.val = β.val
      rw [hαval]
      exact e.inv_hom_id_assoc _⟩

private theorem torus_normalizer_stabilizer_split (corr : BorelsThroughT.{u})
    (reg : RegularCocharacterBorel.{u})
    (A : AffineAlgebraicGroup k) (hA : IsReductive A) {T B : ClosedSubgroup A.val}
    (hs : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T)
    (hB : IsKBorel B) (hTB : IsSubgroupOf T B)
    {g : 𝟙_ (SchemeOver k) ⟶ A.val.X} (hgT : Normalizes T.inclusion g)
    (hgB : ConjugatesSubgroups g B B) : FactorsThrough T g := by
  have hT : IsTorus T.group := (isTorus_iff_coordinates (closedSubgroupAlgebraicGroup T)).mpr (torus_of_split hs)
  obtain ⟨cochar, _, hcochar, _, hBroot⟩ := (corr A hA T hs hm).1 B hB hTB
  obtain ⟨e, w, m, he, hw, hmpos, horder⟩ := finite_conjugation_on_characters A hA T hT hs g hgT
  have hroots : Set.MapsTo w (CharacterPairing.absoluteRoots T) (CharacterPairing.absoluteRoots T) := by
    intro χ hχ
    rw [hw]
    exact conjugate_root_mem T he hχ
  have himage : (fun χ : Character T.group ↦ w χ) '' (Subtype.val '' positiveRoots T cochar) =
      Subtype.val '' positiveRoots T cochar := by
    simpa only [hBroot, hw] using subgroupRoots_conjugate_image T he hgB
  have hpos (α : Root T) : 0 < pairing T.group (w α.val) cochar ↔ 0 < pairing T.group α.val cochar := by
    constructor
    · intro h
      have hh : w α.val ∈ Subtype.val '' positiveRoots T cochar :=
        ⟨⟨w α.val, hroots α.property⟩, h, rfl⟩
      rw [← himage] at hh
      obtain ⟨_, ⟨β, hβ, rfl⟩, heq⟩ := hh
      exact (w.injective heq) ▸ (show 0 < pairing T.group β.val cochar from hβ)
    · intro h
      have hh : w α.val ∈ (fun χ : Character T.group ↦ w χ) '' (Subtype.val '' positiveRoots T cochar) :=
        ⟨α.val, ⟨α, h, rfl⟩, rfl⟩
      rw [himage] at hh
      obtain ⟨β, hβ, heq⟩ := hh
      exact heq ▸ (show 0 < pairing T.group β.val cochar from hβ)
  obtain ⟨mu, hmu, hf⟩ := invariant_regular_cocharacter T hs e w m hw hmpos horder cochar hcochar hroots hpos
  obtain ⟨D⟩ := existsLimitDecomposition A (mu ≫ T.inclusion)
  have hD := (reg A hA T hs hm mu hmu D).1
  have hcent : Centralizes (mu ≫ T.inclusion) g := by
    apply (centralizes_iff _ _).mpr
    intro Y y t
    have hh := congrArg (fun z : T.group.X ⟶ A.val.X ↦ t ≫ mu.hom.hom ≫ z) he
    change (t ≫ (mu ≫ e.hom ≫ T.inclusion).hom.hom) = _ at hh
    rw [← Category.assoc mu, hf] at hh
    simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, comp_toUnit] at hh
    have hy : y = toUnit Y := Subsingleton.elim _ _
    rw [hy]
    exact mul_inv_eq_iff_eq_mul.mp hh.symm
  obtain ⟨x, hx⟩ := (D.centralizer_points _ g).mp hcent
  exact factor_trans ⟨x, hx⟩ hD.1

private theorem maximal_torus_in_borel [IsAlgClosed k] (A : AffineAlgebraicGroup k)
    (hA : IsReductive A) (B : ClosedSubgroup A.val) (hB : IsBorel B) :
    ∃ S : ClosedSubgroup B.group, IsMaximalTorus S ∧ IsMaximalTorus (subgroupOfSubgroup B S) := by
  let D := closedSubgroupAlgebraicGroup B
  obtain ⟨_, _, _, _, _, _, ⟨S, hS⟩, _⟩ := LinearAlgebraicGroups.GeometricTorusSplitting.splitting
    D hB.1.1 hB.1.2.1 hB.1.2.2
  have hS' := (solvable_maximal_torus_iff D S).mp hS
  exact ⟨S, hS', (LinearAlgebraicGroups.MaximalToriConjugate.borelMaximalTorusIff A hA.1
    (connected_of_reductive A hA) B hB S).mp hS'⟩

private theorem rational_borel_normalizer_factors [IsAlgClosed k] (corr : BorelsThroughT.{u})
    (reg : RegularCocharacterBorel.{u})
    (A : AffineAlgebraicGroup k) (hA : IsReductive A) (B : ClosedSubgroup A.val) (hB : IsBorel B)
    (S : ClosedSubgroup B.group) (hS : IsMaximalTorus S)
    (hT : IsMaximalTorus (subgroupOfSubgroup B S))
    (g : 𝟙_ (SchemeOver k) ⟶ A.val.X) (hg : Normalizes B.inclusion g) : FactorsThrough B g := by
  let T := subgroupOfSubgroup B S
  have hTB : IsSubgroupOf T B := ⟨S.inclusion, rfl⟩
  obtain ⟨e, he⟩ := conjugates_of_normalizes B hg
  let S' := transportSubgroup e S
  have hS' : IsMaximalTorus S' := maximal_of_square e S S' (Iso.refl _) (Category.id_comp _) hS
  obtain ⟨b, hb⟩ := solvable_tori_conjugate LinearAlgebraicGroups.GeometricTorusSplitting.splitting
    LinearAlgebraicGroups.GeometricTorusSplitting.conjugacy (closedSubgroupAlgebraicGroup B)
    hB.1.1 hB.1.2.1 hB.1.2.2 S' S hS' hS
  let a := b ≫ B.inclusion.hom.hom
  have hh := conjugates_trans (conjugates_transport e he S) (conjugates_in_ambient B hb)
  have hnormT : Normalizes T.inclusion (a * g) := normalizes_of_conjugates_self T hh
  have hnormB : ConjugatesSubgroups (a * g) B B :=
    conjugates_trans ⟨e, he⟩ (conjugates_preserves_borel B b)
  obtain ⟨t, ht⟩ := factor_trans (torus_normalizer_stabilizer_split corr reg A hA (split_of_maximal hT)
    (geometricMaximal_of_maximal A T hT) ((isKBorel_iff_of_isAlgClosed A B).mpr hB) hTB hnormT hnormB) hTB
  change (𝟙_ (SchemeOver k) ⟶ B.group.X) at b
  refine ⟨b⁻¹ * t, ?_⟩
  simp only [MonObj.mul_comp, GrpObj.inv_comp, ht]
  change a⁻¹ * (a * g) = g
  group

private theorem factor_laurent_descends (A : AffineAlgebraicGroup k) (B : ClosedSubgroup A.val)
    (R : TestAlgebra k) (p : GroupPoints A.val (polynomialAlgebra R))
    (hp : FactorsThrough B (mapPoints (polynomialToLaurent R) p)) : FactorsThrough B p := by
  obtain ⟨C, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr A.property.1
  let i := B.inclusion.hom.hom ≫ e.inv
  have hi : IsClosedImmersion i.left := by
    letI := B.isClosedImmersion
    letI : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
    exact IsClosedImmersion.comp _ _
  obtain ⟨I, d, hd⟩ := closedImmersion_over_affineSpec i hi
  let q := (testSpec k).map (quotientProjection I).op
  have hq : d.hom ≫ q ≫ e.hom = B.inclusion.hom.hom := by
    change d.hom ≫ (testSpec k).map (quotientProjection I).op ≫ e.hom = _
    rw [← Category.assoc, ← hd, Category.assoc, e.inv_hom_id, Category.comp_id]
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let f := (F.preimage (p ≫ e.inv)).unop
  have hf : (testSpec k).map f.op = p ≫ e.inv := F.map_preimage _
  have hg : (F.preimage ((mapPoints (polynomialToLaurent R) p) ≫ e.inv)).unop = f ≫ polynomialToLaurent R := by
    apply Quiver.Hom.op_inj
    apply F.map_injective
    rw [Quiver.Hom.op_unop, F.map_preimage, op_comp, Functor.map_comp, hf]
    exact Category.assoc _ _ _
  have hI : I ≤ RingHom.ker (f ≫ polynomialToLaurent R).hom := by
    rw [← hg, ← factorsThrough_affineQuotient]
    obtain ⟨b, hb⟩ := hp
    exact ⟨b ≫ d.hom, by
      change (b ≫ d.hom) ≫ q = _
      have h := congrArg (fun x ↦ x ≫ e.inv) hb
      change b ≫ B.inclusion.hom.hom ≫ e.inv = _ at h
      rw [Category.assoc, ← hd]
      exact h⟩
  obtain ⟨w, hw⟩ := (factorsThrough_affineQuotient I (p ≫ e.inv)).mpr
    (show I ≤ RingHom.ker f.hom from fun x hx ↦ Polynomial.toLaurent_injective
      (show (polynomialToLaurent R).hom (f.hom x) = 0 from hI hx))
  refine ⟨w ≫ d.inv, ?_⟩
  rw [Category.assoc, ← hq, d.inv_hom_id_assoc, ← Category.assoc, hw,
    Category.assoc, e.inv_hom_id, Category.comp_id]

private theorem contracting_normalizer_factors (A : AffineAlgebraicGroup k)
    (B T : ClosedSubgroup A.val) (hTB : IsSubgroupOf T B) (cochar : Cocharacter T.group)
    (E : LimitDecomposition (oppositeCocharacter (cochar ≫ T.inclusion)))
    (R : TestAlgebra k) (u : GroupPoints E.contracting.group R)
    (hu : Normalizes B.inclusion (u ≫ E.contracting.inclusion.hom.hom)) :
    FactorsThrough B (u ≫ E.contracting.inclusion.hom.hom) := by
  let z : GroupPoints A.val R := u ≫ E.contracting.inclusion.hom.hom
  let c := oppositeCocharacter (cochar ≫ T.inclusion)
  obtain ⟨f, hf, h0⟩ := (E.contracting_points R z).mpr ⟨u, rfl⟩
  let zP : GroupPoints A.val (polynomialAlgebra R) := mapPoints (polynomialConstants R) z
  let zL : GroupPoints A.val (laurentAlgebra R) := mapPoints (laurentConstants R) z
  let t : GroupPoints A.val (laurentAlgebra R) :=
    cocharacterPoint c (laurentAlgebra R) (laurentParameter R)
  have hrestrict : mapPoints (polynomialToLaurent R) zP = zL := by
    change mapPoints (polynomialToLaurent R) (mapPoints (polynomialConstants R) z) = zL
    rw [← mapPoints_comp, polynomialConstants_laurent]
  have heval : mapPoints (polynomialEvaluate R 0) zP = z := by
    change mapPoints (polynomialEvaluate R 0) (mapPoints (polynomialConstants R) z) = z
    rw [← mapPoints_comp, polynomialConstants_zero]
    simp [mapPoints]
  have ht : FactorsThrough B t := by
    obtain ⟨j, hj⟩ := hTB
    refine ⟨cocharacterPoint (oppositeCocharacter cochar ≫ j) _ (laurentParameter R), ?_⟩
    change (unitPoint _ _ ≫ (oppositeCocharacter cochar ≫ j).hom.hom) ≫ B.inclusion.hom.hom = _
    change _ = unitPoint _ _ ≫ c.hom.hom
    simp only [oppositeCocharacter, c, Category.assoc]
    change unitPoint _ _ ≫ ((specGroupMap _ ≫ cochar) ≫ j ≫ B.inclusion).hom.hom = _
    rw [hj, Category.assoc]
  obtain ⟨b, hb⟩ := ht
  have hconj : FactorsThrough B (zL⁻¹ * t * zL) := by
    rw [normalizes_iff_sections] at hu
    have h := (hu _ ((testSpec k).map (laurentConstants R).op) b).2
    rw [hb] at h
    exact h
  have hLaurent : FactorsThrough B (mapPoints (polynomialToLaurent R) (zP⁻¹ * f)) := by
    change FactorsThrough B (((groupPointsFunctor k).obj A.val).map (polynomialToLaurent R)
      (zP⁻¹ * f))
    rw [map_mul, map_inv]
    change FactorsThrough B ((mapPoints (polynomialToLaurent R) zP)⁻¹ * mapPoints (polynomialToLaurent R) f)
    rw [hrestrict, hf]
    change FactorsThrough B (zL⁻¹ * (t * zL * t⁻¹))
    obtain ⟨b', hb'⟩ := hconj
    exact ⟨b' * b⁻¹, by rw [MonObj.mul_comp, GrpObj.inv_comp, hb', hb]; group⟩
  obtain ⟨p, hp⟩ := factor_laurent_descends A B R (zP⁻¹ * f) hLaurent
  let a := (testSpec k).map (polynomialEvaluate R 0).op
  have hh : (a ≫ p) ≫ B.inclusion.hom.hom = z⁻¹ := by
    rw [Category.assoc, hp, MonObj.comp_mul, GrpObj.comp_inv]
    change (mapPoints (polynomialEvaluate R 0) zP)⁻¹ * mapPoints (polynomialEvaluate R 0) f = _
    rw [heval, h0, mul_one]
  exact ⟨(a ≫ p)⁻¹, by rw [GrpObj.inv_comp, hh, inv_inv]⟩

private theorem factors_from_big_cell (A : AffineAlgebraicGroup k)
    (B T : ClosedSubgroup A.val) (hTB : IsSubgroupOf T B) (cochar : Cocharacter T.group)
    (E : LimitDecomposition (oppositeCocharacter (cochar ≫ T.inclusion)))
    {Y : SchemeOver k} (p : Y ⟶ E.contracting.group.X ⊗ B.group.X)
    (hp : Normalizes B.inclusion (p ≫ multiplyFactors E.contracting.inclusion B.inclusion)) :
    FactorsThrough B (p ≫ multiplyFactors E.contracting.inclusion B.inclusion) := by
  apply (factorsThroughClosed_iff _ B.isClosedImmersion _).mpr
  intro R a
  let u : Points E.contracting.group.X R := (a ≫ p) ≫ fst _ _
  let b : (testSpec k).obj (op R) ⟶ B.group.X := (a ≫ p) ≫ snd _ _
  let g := p ≫ multiplyFactors E.contracting.inclusion B.inclusion
  have hprod : a ≫ g = (u ≫ E.contracting.inclusion.hom.hom) * (b ≫ B.inclusion.hom.hom) := by
    simp only [g, u, b, multiplyFactors, Category.assoc, MonObj.comp_mul]
  have hn : Normalizes B.inclusion (a ≫ g) := by
    rw [normalizes_iff_sections] at hp ⊢
    intro X x d
    exact hp X (x ≫ a) d
  have hu : Normalizes B.inclusion (u ≫ E.contracting.inclusion.hom.hom) := by
    have hh := normalizes_mul B hn (normalizes_inv B (subgroup_normalizes B ⟨b, rfl⟩))
    rwa [hprod, mul_assoc, mul_inv_cancel, mul_one] at hh
  obtain ⟨c, hc⟩ := contracting_normalizer_factors A B T hTB cochar E R u hu
  change Points B.group.X R at c
  exact ⟨c * b, by rw [MonObj.mul_comp, hc, hprod]⟩

/-- The scheme normalizer of a geometric Borel is the smooth Borel itself. -/
theorem geometricBorelNormalizer_conditional.{v}
    (corr : BorelsThroughT.{v}) (_ : GeometricBorelChamberConjugacy.{v})
    (_ : GeometricBorelRootSubgroups.{v}) (_ : PositiveSystemsFromCocharacters.{v})
    (reg : RegularCocharacterBorel.{v}) : GeometricBorelNormalizer.{v} := by
  intro k _ _ A hA B hB N hN
  obtain ⟨S, hS, hT⟩ := maximal_torus_in_borel A hA B hB
  let T := subgroupOfSubgroup B S
  have hTB : IsSubgroupOf T B := ⟨S.inclusion, rfl⟩
  obtain ⟨cochar, D, _, hsame, _⟩ := (corr A hA T (split_of_maximal hT)
    (geometricMaximal_of_maximal A T hT)).1 B ((isKBorel_iff_of_isAlgClosed A B).mpr hB) hTB
  let c := cochar ≫ T.inclusion
  obtain ⟨E⟩ := existsLimitDecomposition A (oppositeCocharacter c)
  obtain ⟨e, he⟩ := subgroupOf_mutual_iso hsame.1 hsame.2
  let m := multiplyFactors E.contracting.inclusion B.inclusion
  haveI : Smooth A.val.X.hom := hA.1
  haveI : IsOpenImmersion m.left := by
    let a : B.group.X ⟶ D.parabolic.group.X := e.hom.hom.hom
    let l := lift (fst E.contracting.group.X B.group.X) (snd _ _ ≫ a)
    have he' : a ≫ D.parabolic.inclusion.hom.hom = B.inclusion.hom.hom :=
      congrArg (fun f : B.group ⟶ A.val ↦ f.hom.hom) he
    have hl : m = l ≫ multiplyFactors E.contracting.inclusion D.parabolic.inclusion := by
      simp only [m, l, multiplyFactors, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, Category.assoc, he']
    rw [hl, Over.comp_left]
    haveI : IsOpenImmersion (multiplyFactors E.contracting.inclusion D.parabolic.inclusion).left :=
      multiply_isOpenImmersion A c D E
    haveI : IsIso a := (Grp.forget (SchemeOver k)).map_isIso e.hom
    haveI : IsIso l := by
      change IsIso (E.contracting.group.X ◁ a)
      infer_instance
    haveI : IsIso l.left := (Over.forget _).map_isIso l
    infer_instance
  have hBN : IsSubgroupOf B N := by
    obtain ⟨b, hb⟩ := (hN _ B.inclusion.hom.hom).mp (subgroup_normalizes B ⟨𝟙 _, Category.id_comp _⟩)
    exact factor_group_through_subgroup N B.inclusion b hb
  have hNF : FactorsThrough B N.inclusion.hom.hom := by
    let C := closedSubgroupAlgebraicGroup N
    let V : Set N.group.X.left := N.inclusion.hom.hom.left ⁻¹' Set.range m.left
    have hV : IsOpen V := m.left.isOpenEmbedding.isOpen_range.preimage N.inclusion.hom.hom.left.continuous
    letI : LocallyOfFiniteType N.group.X.hom := C.property.2.1
    haveI : JacobsonSpace N.group.X.left := LocallyOfFiniteType.jacobsonSpace N.group.X.hom
    have hclosed : closedPoints N.group.X.left ⊆ V := by
      intro x hx
      let p := sectionOfClosedPoint N.group.X x hx
      have hn := (hN _ (p ≫ N.inclusion.hom.hom)).mpr ⟨p, rfl⟩
      obtain ⟨b, hb⟩ := rational_borel_normalizer_factors corr reg A hA B hB S hS hT _ hn
      have hh : lift (1 : 𝟙_ (SchemeOver k) ⟶ E.contracting.group.X) b ≫ m =
          p ≫ N.inclusion.hom.hom := by
        simp only [m, multiplyFactors, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, hb,
          MonObj.one_comp, one_mul]
      refine ⟨(lift (1 : 𝟙_ (SchemeOver k) ⟶ E.contracting.group.X) b).left (IsLocalRing.closedPoint k), ?_⟩
      have h := congrArg (fun f : 𝟙_ (SchemeOver k) ⟶ A.val.X ↦ f.left (IsLocalRing.closedPoint k)) hh
      change _ = N.inclusion.hom.hom.left (p.left (IsLocalRing.closedPoint k)) at h
      simpa only [Over.comp_left, Scheme.Hom.comp_apply, p, sectionOfClosedPoint_apply] using h
    have hVall : V = Set.univ := by
      by_contra h
      obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints
        (Z := Vᶜ) (Set.nonempty_compl.mpr h) hV.isClosed_compl.isLocallyClosed
      exact hx (hclosed hxc)
    have hrange : Set.range N.inclusion.hom.hom.left ⊆ Set.range m.left := by
      rintro x ⟨y, rfl⟩
      change y ∈ V
      rw [hVall]
      trivial
    let l := IsOpenImmersion.lift m.left N.inclusion.hom.hom.left hrange
    have hl : l ≫ m.left = N.inclusion.hom.hom.left := IsOpenImmersion.lift_fac _ _ _
    let p : N.group.X ⟶ E.contracting.group.X ⊗ B.group.X := Over.homMk l (by
      rw [← Over.w m, ← Category.assoc, hl, Over.w])
    have hcomp : p ≫ m = N.inclusion.hom.hom := Over.OverMorphism.ext hl
    rw [← hcomp]
    exact factors_from_big_cell A B T hTB cochar E p (hcomp.symm ▸ (hN _ _).mpr ⟨𝟙 _, Category.id_comp _⟩)
  obtain ⟨n, hn⟩ := hNF
  have hNB := factor_group_through_subgroup B N.inclusion n hn
  obtain ⟨e', _⟩ := subgroupOf_mutual_iso hNB hBN
  let j := (Grp.forget (SchemeOver k) ⋙ Over.forget _).mapIso e'
  refine ⟨?_, hNB, hBN⟩
  rw [← Over.w e'.hom.hom.hom]
  letI : Smooth B.group.X.hom := hB.1.1
  haveI : IsIso e'.hom.hom.hom.left := inferInstanceAs (IsIso j.hom)
  infer_instance

private theorem normal_precompose_iso {H I : GroupScheme k} (e : H ≅ I) (i : I ⟶ G)
    (hi : IsNormalSubgroup i) : IsNormalSubgroup (e.hom ≫ i) := by
  obtain ⟨c, hc⟩ := hi
  let f := G.X ◁ e.hom.hom.hom
  refine ⟨f ≫ c ≫ e.inv.hom.hom, ?_⟩
  have he : e.inv.hom.hom ≫ (e.hom ≫ i).hom.hom = i.hom.hom := by
    change (e.inv ≫ e.hom ≫ i).hom.hom = _
    rw [e.inv_hom_id_assoc]
  rw [Category.assoc, Category.assoc, he, hc]
  simp only [subgroupConjugation, MonObj.comp_mul, GrpObj.comp_inv, f,
    whiskerLeft_fst, whiskerLeft_snd_assoc]
  rfl

private theorem reductive_geometric (A : AffineAlgebraicGroup k) (hA : IsReductive A) :
    IsReductive (GeometricGroup A) := by
  let K := AlgebraicClosure k
  let H := GeometricGroup A
  have hs : Smooth H.val.X.hom := (smooth_extend_iff K A.val.X).mpr hA.1
  have hc : GeometricallyConnected H.val.X.hom := by
    letI := hA.2.1
    exact inferInstanceAs (GeometricallyConnected (pullback.snd A.val.X.hom (fieldSpecMap k K)))
  refine ⟨hs, hc, ?_⟩
  let V := GeometricRadicals.geometricUnipotentRadical H
  have hV := LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest H
  obtain ⟨U, e, he⟩ := pullback_subgroup_over_closed_field H V
  let L := AlgebraicClosure K
  let U' := extendSubgroup L U
  let D := closedSubgroupAlgebraicGroup U
  let J := (Grp.forget (SchemeOver L) ⋙ Over.forget _).mapIso e
  have hsU' : Smooth U'.group.X.hom := by
    rw [← Over.w e.hom.hom.hom]
    letI : Smooth V.group.X.hom := hV.1.1
    haveI : IsIso e.hom.hom.hom.left := inferInstanceAs (IsIso J.hom)
    infer_instance
  have hcU' : ConnectedSpace U'.group.X.left := J.hom.homeomorph.connectedSpace_iff.mpr hV.1.2.1
  have hU : GeometricRadicals.IsSmoothConnectedNormal U := by
    letI : IsIso (fieldSpecMap K L) := fieldSpecMap_isIso
    refine ⟨(smooth_extend_iff L U.group.X).mp hsU', (connected_extend_iso_iff L U.group.X).mp hcU', ?_⟩
    apply (baseChangeNormalSubgroupIff K L U.inclusion U.isClosedImmersion).mp
    change IsNormalSubgroup U'.inclusion
    rw [← he]
    exact normal_precompose_iso e V.inclusion hV.1.2.2
  have hUD : Unipotent.IsUnipotent D := by
    apply (LinearAlgebraicGroups.Unipotent.unipotenceFieldExtension (K := L) D).mp
    obtain ⟨R, ⟨i⟩, hi⟩ := hV.2.1
    exact ⟨R, ⟨i ≪≫ e.symm⟩, hi⟩
  let U₀ := GeometricRadicals.geometricUnipotentRadical A
  obtain ⟨j, hj⟩ := (LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest A).2.2 U hU hUD
  obtain ⟨triv⟩ := hA.2.2
  have hz : IsZero U₀.group := (Grp.isZero_trivial _).of_iso triv
  have hi : U.inclusion = 0 := by rw [← hj, hz.eq_of_tgt j 0, zero_comp]
  letI : Mono U.inclusion := (Grp.forget (SchemeOver K)).mono_of_mono_map
    (show Mono U.inclusion.hom.hom from mono_over _ U.isClosedImmersion)
  have hUzero := IsZero.of_mono_eq_zero U.inclusion hi
  let F := groupBaseChange K L
  letI : F.IsEquivalence := groupBaseChange_isEquivalence
  have hter : IsTerminal (F.obj U.group) := hUzero.isTerminal.isTerminalObj F
  exact ⟨e.symm ≪≫ hter.uniqueUpToIso (Grp.isZero_trivial (SchemeOver L)).isTerminal⟩

/-- A geometric conjugation through a split torus can be lifted over the
ground field by lifting its label in the constant Weyl quotient. -/
private theorem rational_borel_conjugacy (geo : GeometricBorelChamberConjugacy.{u})
    (A : AffineAlgebraicGroup k) (hA : IsReductive A) (T : ClosedSubgroup A.val)
    (hs : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T)
    (B C : ClosedSubgroup A.val) (hB : IsKBorel B) (hC : IsKBorel C)
    (hTB : IsSubgroupOf T B) (hTC : IsSubgroupOf T C) :
    ∃ g : 𝟙_ (SchemeOver k) ⟶ A.val.X,
      Normalizes T.inclusion g ∧ ConjugatesSubgroups g B C := by
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let T' := extendSubgroup K T
  let B' := extendSubgroup K B
  let C' := extendSubgroup K C
  obtain ⟨_, hT' : IsMaximalTorus T'⟩ := hm
  obtain ⟨_, hB' : IsBorel B'⟩ := hB
  obtain ⟨_, hC' : IsBorel C'⟩ := hC
  have hs' : IsSplitTorus T'.group := split_of_maximal (A := GeometricGroup A) (T := T') hT'
  obtain ⟨g', _, hg'T, hg'BC, _, _⟩ := geo (GeometricGroup A) (reductive_geometric A hA)
    T' hs' (geometricMaximal_of_maximal (GeometricGroup A) T' hT')
    B' C' hB' hC' (subgroup_extend K hTB) (subgroup_extend K hTC)
  change (𝟙_ (SchemeOver K) ⟶ (F.obj A.val).X) at g'
  have hT : IsTorus T.group :=
    (isTorus_iff_coordinates (closedSubgroupAlgebraicGroup T)).mpr (torus_of_split hs)
  obtain ⟨N, j, hj, W, q, hN, hjN, hq, _, _, _, hsplit⟩ :=
    LinearAlgebraicGroups.Reductive.WeylScheme.weylScheme A hA T hT ⟨T'.isClosedImmersion, hT'⟩
  obtain ⟨⟨I⟩, hlift⟩ := hsplit hs
  obtain ⟨_, hN'⟩ := normalizerSchemeBaseChange k K T.inclusion N T.isClosedImmersion hN
  obtain ⟨b, hb⟩ := (hN' _ g').mp hg'T
  change (𝟙_ (SchemeOver K) ⟶ (F.obj N.group).X) at b
  let d := (F.map N.inclusion).hom.hom
  let j' := (F.map j).hom.hom
  let q' := (F.map q).hom.hom
  have hj' : j' ≫ d = T'.inclusion.hom.hom := by
    change (F.map j ≫ F.map N.inclusion).hom.hom = (F.map T.inclusion).hom.hom
    rw [← Functor.map_comp, hjN]
  obtain ⟨w, hw⟩ := constant_sections_after_scalar_extension I.constantGroup K (b ≫ q')
  obtain ⟨a, ha⟩ := (hlift (I.constantGroup.sectionPoint w)).2
  let g := a ≫ N.inclusion.hom.hom
  let gK : 𝟙_ (SchemeOver K) ⟶ (F.obj A.val).X := scalarExtendedRationalPoint K g
  let a' : 𝟙_ (SchemeOver K) ⟶ (F.obj N.group).X := scalarExtendedRationalPoint K a
  have ha' : a' ≫ q' = b ≫ q' := by
    change scalarExtendedRationalPoint K a ≫ (baseChange k K).map q.hom.hom = _
    rw [← scalarExtendedPoint_natural, ha, hw]
  haveI : IsMonHom d := inferInstanceAs (IsMonHom (F.map N.inclusion).hom.hom)
  haveI : IsMonHom q' := inferInstanceAs (IsMonHom (F.map q).hom.hom)
  let p : 𝟙_ (SchemeOver K) ⟶ (F.obj N.group).X := a'⁻¹ * b
  have hp : p ≫ q' = toUnit (𝟙_ (SchemeOver K)) ≫ η[(F.obj W.val).X] := by
    change (a'⁻¹ * b) ≫ q' = _
    rw [MonObj.mul_comp, GrpObj.inv_comp, ha', inv_mul_cancel, CategoryTheory.Hom.one_def]
  have hker : IsPullback j' (toUnit _) q' η[(F.obj W.val).X] :=
    baseChangeKernelSquare q j hq.1
  have hfactor : FactorsThrough T' (gK⁻¹ * g') := by
    have hg : gK = a' ≫ d :=
      scalarExtendedPoint_natural K a N.inclusion.hom.hom
    change b ≫ d = g' at hb
    refine ⟨hker.lift p (toUnit _) hp, ?_⟩
    change hker.lift p (toUnit _) hp ≫ T'.inclusion.hom.hom = _
    rw [← hj', ← Category.assoc, hker.lift_fst, hg, ← hb, ← GrpObj.inv_comp, ← MonObj.mul_comp]
  obtain ⟨t, ht⟩ := factor_trans hfactor (subgroup_extend K hTB)
  have hstab := conjugates_preserves_borel B' t
  change t ≫ B'.inclusion.hom.hom = gK⁻¹ * g' at ht
  rw [ht] at hstab
  have hconj := conjugates_trans (conjugates_inverse hstab) hg'BC
  rw [mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul] at hconj
  exact ⟨g, (hN _ _).mpr ⟨a, rfl⟩, conjugates_descend K (g := g) hconj⟩

/-- Scheme normalizer equality descends to the original field. -/
theorem groundFieldBorelNormalizer_conditional.{v}
    (corr : BorelsThroughT.{v}) (geo : GeometricBorelChamberConjugacy.{v})
    (roots : GeometricBorelRootSubgroups.{v}) (positive : PositiveSystemsFromCocharacters.{v})
    (reg : RegularCocharacterBorel.{v}) : GroundFieldBorelNormalizer.{v} := by
  intro k _ A hA B hB
  let K := AlgebraicClosure k
  obtain ⟨N, hN⟩ := normalizerScheme k A B
  obtain ⟨_, hNK : RepresentsSubgroup (extendSubgroup K N) (fun _ g ↦
    Normalizes (extendSubgroup K B).inclusion g)⟩ :=
    normalizerSchemeBaseChange k K B.inclusion N B.isClosedImmersion hN
  obtain ⟨_, hBK : IsBorel (extendSubgroup K B)⟩ := hB
  have he := (geometricBorelNormalizer_conditional corr geo roots positive reg (GeometricGroup A)
    (reductive_geometric A hA) (extendSubgroup K B) hBK (extendSubgroup K N) hNK).2
  intro X g
  exact ⟨fun h ↦ factor_trans ((hN X g).mp h) (subgroup_descend K he.1), subgroup_normalizes B⟩

/-- Geometric normalizer representatives give exactly one right torus coset. -/
theorem geometricWeylSimplyTransitiveOnBorels_conditional.{v}
    (corr : BorelsThroughT.{v}) (geo : GeometricBorelChamberConjugacy.{v})
    (_ : GeometricBorelRootSubgroups.{v}) (_ : PositiveSystemsFromCocharacters.{v})
    (reg : RegularCocharacterBorel.{v}) : GeometricWeylSimplyTransitiveOnBorels.{v} := by
  intro k _ _ A hA T hT
  have hc := connected_of_reductive A hA
  refine ⟨LinearAlgebraicGroups.GeometricBorelConjugacy.torusContainedInBorel A hA.1 hc T hT.1, ?_⟩
  intro B C hB hC hTB hTC
  obtain ⟨g, _, hgT, hg, _, _⟩ := geo A hA T (split_of_maximal hT)
    (geometricMaximal_of_maximal A T hT) B C hB hC hTB hTC
  refine ⟨g, hgT, hg, fun g' hg'T ↦ conjugation_coset T B C hTB (fun _ hn h ↦ ?_) hgT hg hg'T⟩
  exact torus_normalizer_stabilizer_split corr reg A hA (split_of_maximal hT)
    (geometricMaximal_of_maximal A T hT) ((isKBorel_iff_of_isAlgClosed A B).mpr hB) hTB hn h

/-- Over the ground field, alignment and the stabilizer calculation give simple transitivity. -/
theorem weylSimplyTransitiveOnBorels_conditional.{v}
    (corr : BorelsThroughT.{v}) (geo : GeometricBorelChamberConjugacy.{v})
    (_ : GeometricBorelRootSubgroups.{v}) (_ : PositiveSystemsFromCocharacters.{v})
    (reg : RegularCocharacterBorel.{v}) : WeylSimplyTransitiveOnBorels.{v} := by
  intro k _ A hA T hs hm
  obtain ⟨cochar, hcochar⟩ := exists_regular_cocharacter A T hs
  obtain ⟨D⟩ := existsLimitDecomposition A (cochar ≫ T.inclusion)
  have hD := reg A hA T hs hm cochar hcochar D
  refine ⟨⟨D.parabolic, hD.2.1, hD.2.2.1⟩, ?_⟩
  intro B C hB hC hTB hTC
  obtain ⟨g, hgT, hg⟩ := rational_borel_conjugacy geo A hA T hs hm B C hB hC hTB hTC
  exact ⟨g, hgT, hg, fun g' hg'T ↦ conjugation_coset T B C hTB
    (fun _ hn h ↦ torus_normalizer_stabilizer_split corr reg A hA hs hm hB hTB hn h) hgT hg hg'T⟩

private theorem subgroupRoots_conjugate {A : AffineAlgebraicGroup k} {T B : ClosedSubgroup A.val}
    (hB : IsKBorel B) (hTB : IsSubgroupOf T B)
    {g : 𝟙_ (SchemeOver k) ⟶ A.val.X} {e : T.group ≅ T.group}
    (he : InducesTorusConjugation T g e) :
    let C := transportSubgroup (conjugationIso g) B
    IsKBorel C ∧ IsSubgroupOf T C ∧
      (fun χ : Character T.group ↦ e.inv ≫ χ) '' (Subtype.val '' subgroupRoots T B) =
        Subtype.val '' subgroupRoots T C := by
  let C := transportSubgroup (conjugationIso g) B
  have hBC : ConjugatesSubgroups g B C := conjugates_transport_ambient B g
  have hC := conjugate_isKBorel B hB g
  have hTC := subgroup_conjugate hTB ⟨e, he⟩ hBC
  exact ⟨hC, hTC, subgroupRoots_conjugate_image T he hBC⟩

/-- Inverse pullback on characters carries positive systems simply transitively. -/
theorem weylSimplyTransitiveOnPositiveSystems_conditional.{v}
    (corr : BorelsThroughT.{v}) (geo : GeometricBorelChamberConjugacy.{v})
    (roots : GeometricBorelRootSubgroups.{v}) (positive : PositiveSystemsFromCocharacters.{v})
    (reg : RegularCocharacterBorel.{v}) : WeylSimplyTransitiveOnPositiveSystems.{v} := by
  intro k _ A hA T hs hm
  obtain ⟨cochar, hcochar⟩ := exists_regular_cocharacter A T hs
  refine ⟨⟨positiveRoots T cochar, (positive A hA T hs hm _).mpr ⟨cochar, hcochar, rfl⟩⟩, ?_, ?_⟩
  · intro S hS g hg
    obtain ⟨B, hB, hTB, hBS, _⟩ := ((corr A hA T hs hm).2 S).mp hS
    obtain ⟨e, he⟩ := conjugates_of_normalizes T hg
    have he' : InducesTorusConjugation T g e := he
    obtain ⟨hC, hTC, him⟩ := subgroupRoots_conjugate hB hTB he'
    let C := transportSubgroup (conjugationIso g) B
    obtain ⟨mu, _, hmu, _, hCmu⟩ := (corr A hA T hs hm).1 C hC hTC
    exact ⟨e, subgroupRoots T C, he', (positive A hA T hs hm _).mpr ⟨mu, hmu, hCmu.symm⟩, hBS ▸ him⟩
  · intro S₁ S₂ hS₁ hS₂
    obtain ⟨B, hB, hTB, hBS, _⟩ := ((corr A hA T hs hm).2 S₁).mp hS₁
    obtain ⟨C, hC, hTC, hCS, huniq⟩ := ((corr A hA T hs hm).2 S₂).mp hS₂
    obtain ⟨g, hgT, hg, hcoset⟩ := (weylSimplyTransitiveOnBorels_conditional corr geo roots positive reg
      A hA T hs hm).2 B C hB hC hTB hTC
    obtain ⟨e, he⟩ := conjugates_of_normalizes T hgT
    have forward {n : 𝟙_ (SchemeOver k) ⟶ A.val.X} {d : T.group ≅ T.group}
        (hd : InducesTorusConjugation T n d) (hn : ConjugatesSubgroups n B C) :
        (fun χ : Character T.group ↦ d.inv ≫ χ) '' (Subtype.val '' S₁) = Subtype.val '' S₂ := by
      simpa only [hBS, hCS] using subgroupRoots_conjugate_image T hd hn
    refine ⟨g, e, hgT, he, forward he hg, fun g' e' hg'T he' ↦ ?_⟩
    rw [← hcoset g' hg'T]
    refine ⟨fun h ↦ ?_, forward he'⟩
    let C' := transportSubgroup (conjugationIso g') B
    obtain ⟨hC', hTC', hC'S⟩ := subgroupRoots_conjugate hB hTB he'
    have eq : Subtype.val '' subgroupRoots T C' = Subtype.val '' S₂ := by
      rw [← hC'S, hBS, h]
    have heq : subgroupRoots T C' = S₂ := (Set.image_injective.mpr Subtype.val_injective) eq
    obtain ⟨hCC', hC'C⟩ := huniq C' hC' hTC' heq
    exact conjugates_of_same (conjugates_transport_ambient B g') ⟨hC'C, hCC'⟩

end

end LinearAlgebraicGroups.RootData.BorelNormalizer

universe v8_closure_ca309ed2a154cc99_u0
theorem _root_.«LinearAlgebraicGroups».«RootData».«BorelNormalizer».«borelNormalizerIntersection» : _root_.«LinearAlgebraicGroups».«Specs».«BorelNormalizer».«BorelNormalizerIntersection».{v8_closure_ca309ed2a154cc99_u0} :=
  @_root_.«LinearAlgebraicGroups».«RootData».«BorelNormalizer».«borelNormalizerIntersection_conditional».{v8_closure_ca309ed2a154cc99_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«borelsThroughT».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«geometricBorelChamberConjugacy».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«geometricBorelRootSubgroups».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«positiveSystemsFromCocharacters».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«regularCocharacterBorel».{v8_closure_ca309ed2a154cc99_u0})
theorem _root_.«LinearAlgebraicGroups».«RootData».«BorelNormalizer».«geometricBorelNormalizer» : _root_.«LinearAlgebraicGroups».«Specs».«BorelNormalizer».«GeometricBorelNormalizer».{v8_closure_ca309ed2a154cc99_u0} :=
  @_root_.«LinearAlgebraicGroups».«RootData».«BorelNormalizer».«geometricBorelNormalizer_conditional».{v8_closure_ca309ed2a154cc99_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«borelsThroughT».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«geometricBorelChamberConjugacy».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«geometricBorelRootSubgroups».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«positiveSystemsFromCocharacters».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«regularCocharacterBorel».{v8_closure_ca309ed2a154cc99_u0})
theorem _root_.«LinearAlgebraicGroups».«RootData».«BorelNormalizer».«geometricWeylSimplyTransitiveOnBorels» : _root_.«LinearAlgebraicGroups».«Specs».«BorelNormalizer».«GeometricWeylSimplyTransitiveOnBorels».{v8_closure_ca309ed2a154cc99_u0} :=
  @_root_.«LinearAlgebraicGroups».«RootData».«BorelNormalizer».«geometricWeylSimplyTransitiveOnBorels_conditional».{v8_closure_ca309ed2a154cc99_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«borelsThroughT».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«geometricBorelChamberConjugacy».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«geometricBorelRootSubgroups».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«positiveSystemsFromCocharacters».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«regularCocharacterBorel».{v8_closure_ca309ed2a154cc99_u0})
theorem _root_.«LinearAlgebraicGroups».«RootData».«BorelNormalizer».«groundFieldBorelNormalizer» : _root_.«LinearAlgebraicGroups».«Specs».«BorelNormalizer».«GroundFieldBorelNormalizer».{v8_closure_ca309ed2a154cc99_u0} :=
  @_root_.«LinearAlgebraicGroups».«RootData».«BorelNormalizer».«groundFieldBorelNormalizer_conditional».{v8_closure_ca309ed2a154cc99_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«borelsThroughT».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«geometricBorelChamberConjugacy».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«geometricBorelRootSubgroups».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«positiveSystemsFromCocharacters».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«regularCocharacterBorel».{v8_closure_ca309ed2a154cc99_u0})
theorem _root_.«LinearAlgebraicGroups».«RootData».«BorelNormalizer».«lieQuotientZeroWeight» : _root_.«LinearAlgebraicGroups».«Specs».«BorelNormalizer».«LieQuotientZeroWeight».{v8_closure_ca309ed2a154cc99_u0} :=
  @_root_.«LinearAlgebraicGroups».«RootData».«BorelNormalizer».«lieQuotientZeroWeight_conditional».{v8_closure_ca309ed2a154cc99_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«borelsThroughT».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«geometricBorelChamberConjugacy».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«geometricBorelRootSubgroups».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«positiveSystemsFromCocharacters».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«regularCocharacterBorel».{v8_closure_ca309ed2a154cc99_u0})
theorem _root_.«LinearAlgebraicGroups».«RootData».«BorelNormalizer».«weylSimplyTransitiveOnBorels» : _root_.«LinearAlgebraicGroups».«Specs».«BorelNormalizer».«WeylSimplyTransitiveOnBorels».{v8_closure_ca309ed2a154cc99_u0} :=
  @_root_.«LinearAlgebraicGroups».«RootData».«BorelNormalizer».«weylSimplyTransitiveOnBorels_conditional».{v8_closure_ca309ed2a154cc99_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«borelsThroughT».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«geometricBorelChamberConjugacy».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«geometricBorelRootSubgroups».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«positiveSystemsFromCocharacters».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«regularCocharacterBorel».{v8_closure_ca309ed2a154cc99_u0})
theorem _root_.«LinearAlgebraicGroups».«RootData».«BorelNormalizer».«weylSimplyTransitiveOnPositiveSystems» : _root_.«LinearAlgebraicGroups».«Specs».«BorelNormalizer».«WeylSimplyTransitiveOnPositiveSystems».{v8_closure_ca309ed2a154cc99_u0} :=
  @_root_.«LinearAlgebraicGroups».«RootData».«BorelNormalizer».«weylSimplyTransitiveOnPositiveSystems_conditional».{v8_closure_ca309ed2a154cc99_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«borelsThroughT».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«geometricBorelChamberConjugacy».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«geometricBorelRootSubgroups».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«positiveSystemsFromCocharacters».{v8_closure_ca309ed2a154cc99_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelsAndChambers».«regularCocharacterBorel».{v8_closure_ca309ed2a154cc99_u0})
