import LinearAlgebraicGroups.Flag.SmoothOrbit
import Specs.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
import Specs.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
import LinearAlgebraicGroups.Affine.FaithfulLinearization
import LinearAlgebraicGroups.Affine.Stabilizers
import LinearAlgebraicGroups.Reductive.BorelProper
import LinearAlgebraicGroups.Reductive.CocharacterDynamics
import LinearAlgebraicGroups.Reductive.MaximalToriConjugate
import Mathlib.Algebra.Polynomial.Roots
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection

open _root_.LinearAlgebraicGroups.Specs
open Specs.UnipotentRadicalIntersection
open Specs.GeometricBorelConjugacy
open Specs.GeometricRadicals (IsMaximalTorus IsSmoothConnectedNormal IsUnipotentRadical)
open Specs.SchemeDerivedGroup (IsSubgroupOf IsSolvable)
open Specs.Unipotent (IsUnipotent closedSubgroupAlgebraicGroup)
open Specs.NormalizerLatticeAction
open Specs.GeometricRadicals (IsSolvableRadical)
noncomputable section
variable {k : Type u} [Field k]
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
private theorem sections_transport {G : GroupScheme k} {H : ClosedSubgroup G}
    {A : GroupScheme k} (j : A ⟶ G) (e : H.group ≅ A)
    (he : e.hom ≫ j = H.inclusion) {Y : SchemeOver k} {y : Y ⟶ G.X} :
    y ∈ SubgroupSections H Y ↔ ∃ a : Y ⟶ A.X, a ≫ j.hom.hom = y := by
  have he' := congrArg (Grp.forget (SchemeOver k)).map he
  change e.hom.hom.hom ≫ j.hom.hom = H.inclusion.hom.hom at he'
  constructor
  · rintro ⟨b, rfl⟩
    refine ⟨b ≫ e.hom.hom.hom, ?_⟩
    change (b ≫ e.hom.hom.hom) ≫ j.hom.hom = b ≫ H.inclusion.hom.hom
    rw [Category.assoc, he']
  · rintro ⟨a, rfl⟩
    refine ⟨a ≫ e.inv.hom.hom, ?_⟩
    change (a ≫ e.inv.hom.hom) ≫ H.inclusion.hom.hom = a ≫ j.hom.hom
    have hcancel : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 A.X :=
      congrArg (Grp.forget (SchemeOver k)).map e.inv_hom_id
    rw [Category.assoc, ← he', ← Category.assoc e.inv.hom.hom e.hom.hom.hom,
      hcancel, Category.id_comp]

private theorem schemeIntersection_exists (G : AffineAlgebraicGroup k)
    (family : Set (ClosedSubgroup G.val)) :
    ∃ I : ClosedSubgroup G.val, IsSchemeIntersection family I := by
  classical
  obtain ⟨A', ⟨e⟩⟩ := essImage_hopfSpec.mpr G.property.1
  let A := A'.unop
  let E : (specGroup A).X ≅ G.val.X := (Grp.forget (SchemeOver k)).mapIso e
  let X := family
  let j (H : X) := H.val.inclusion ≫ e.inv
  have hclosed (H : X) : IsClosedImmersion (j H).hom.hom.left := by
    letI := H.val.isClosedImmersion
    haveI : IsIso e.inv.hom.hom.left :=
      (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso e.inv
    exact IsClosedImmersion.comp H.val.inclusion.hom.hom.left e.inv.hom.hom.left
  have hclass (H : X) := (closedSubgroupClassification k A H.val.group (j H)).mp (hclosed H)
  let K (H : X) : Ideal A := (hclass H).exists.choose
  have hK (H : X) : ∃ (_ : (K H).IsHopfIdeal k),
      ∃ b : H.val.group ≅ specGroup (hopfQuotient A (K H)),
        b.hom ≫ specGroupMap (hopfQuotientMap A (K H)) = j H :=
    (hclass H).exists.choose_spec
  letI (H : X) : (K H).IsHopfIdeal k := (hK H).choose
  let b (H : X) := (hK H).choose_spec.choose
  have hb (H : X) :
      (b H).hom ≫ specGroupMap (hopfQuotientMap A (K H)) ≫ e.hom = H.val.inclusion := by
    rw [← Category.assoc, (hK H).choose_spec.choose_spec]
    simp [j]
  obtain ⟨hL, p, hp, _, ⟨hc⟩⟩ := subgroupFamilyIntersection k A K
  letI := hL
  let q := specGroupMap (hopfQuotientMap A (⨆ H, K H))
  let i := q ≫ e.hom
  haveI : IsClosedImmersion q.hom.hom.left :=
    (hopfMapClosedImmersion k _).mpr Ideal.Quotient.mk_surjective
  haveI : IsIso e.hom.hom.hom.left :=
    (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso e.hom
  refine ⟨⟨_, i, IsClosedImmersion.comp q.hom.hom.left e.hom.hom.hom.left⟩, ?_⟩
  intro Y y
  constructor
  · rintro ⟨z, rfl⟩ H hH
    let H' : X := ⟨H, hH⟩
    have h : p H' ≫ specGroupMap (hopfQuotientMap A (K H')) ≫ e.hom = i := by
      rw [← Category.assoc, hp H']
    apply (sections_transport _ (b H') (hb H')).mpr
    exact ⟨z ≫ (p H').hom.hom, by
      rw [Category.assoc]
      exact congrArg (fun f : _ ⟶ G.val ↦ z ≫ f.hom.hom) h⟩
  · intro hy
    have hy' (H : X) : ∃ z : Y ⟶ (specGroup (hopfQuotient A (K H))).X,
        z ≫ (specGroupMap (hopfQuotientMap A (K H))).hom.hom = y ≫ E.inv := by
      obtain ⟨z, hz⟩ := (sections_transport _ (b H) (hb H)).mp (hy H.val H.property)
      refine ⟨z, ?_⟩
      apply (cancel_mono E.hom).mp
      rw [Category.assoc, Category.assoc, E.inv_hom_id, Category.comp_id]
      exact hz
    have hc' : IsLimit ((Grp.forget (SchemeOver k)).mapCone
        (WidePullbackCone.mk q p hp)) := hc
    let t : Cone (WidePullbackShape.wideCospan (specGroup A)
        (fun H : X ↦ specGroup (hopfQuotient A (K H)))
        (fun H ↦ specGroupMap (hopfQuotientMap A (K H))) ⋙ Grp.forget (SchemeOver k)) :=
      WidePullbackShape.mkCone (y ≫ E.inv) (fun H ↦ (hy' H).choose)
        (fun H ↦ (hy' H).choose_spec)
    have hz : hc'.lift t ≫ q.hom.hom = y ≫ E.inv := hc'.fac t none
    refine ⟨hc'.lift t, ?_⟩
    change hc'.lift t ≫ q.hom.hom ≫ E.hom = y
    rw [← Category.assoc, hz, Category.assoc, E.inv_hom_id]
    exact Category.comp_id _

open private exists_borel_above reducedComponent_spec subgroupOf_trans
  factor_group_through_subgroup conjugation conjugation_apply conjugate conjugate_inclusion
  conjugate_subgroupOf conjugate_inv_cancel borel_conjugate torus_smooth_connected_solvable
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private ReducedIdentityComponent.factorHom
  from LinearAlgebraicGroups.Solvable.EquivariantUnipotentSeries
open private factor_closed factor_normal solvable_iff_sections rationalMap rationalSections
  from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private split_solvable_points from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private splitSolvable_of_additiveSeries from LinearAlgebraicGroups.Solvable.BorelFixedPoint
open private affineBaseTerminal from LinearAlgebraicGroups.Solvable.SplitFixedPoint
open private sectionOfClosedPoint sectionOfClosedPoint_apply
  from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open scoped CategoryTheory.GrpObj

private theorem sections_of_subgroup {G : GroupScheme k} {H N : ClosedSubgroup G}
    (h : IsSubgroupOf H N) {X : SchemeOver k} {x : X ⟶ G.X}
    (hx : x ∈ SubgroupSections H X) : x ∈ SubgroupSections N X := by
  change (∃ v : X ⟶ H.group.X, v ≫ H.inclusion.hom.hom = x) at hx
  change ∃ v : X ⟶ N.group.X, v ≫ N.inclusion.hom.hom = x
  obtain ⟨j, hj⟩ := h
  obtain ⟨v, rfl⟩ := hx
  refine ⟨v ≫ j.hom.hom, ?_⟩
  rw [Category.assoc]
  exact congrArg (fun a : H.group ⟶ G ↦ v ≫ a.hom.hom) hj

private theorem inclusion_mem_sections {G : GroupScheme k} (H : ClosedSubgroup G) :
    H.inclusion.hom.hom ∈ SubgroupSections H H.group.X := by
  change ∃ v : H.group.X ⟶ H.group.X, v ≫ H.inclusion.hom.hom = H.inclusion.hom.hom
  exact ⟨𝟙 _, Category.id_comp _⟩

private theorem subgroup_of_sections {G : GroupScheme k} {H N : ClosedSubgroup G}
    (h : H.inclusion.hom.hom ∈ SubgroupSections N H.group.X) : IsSubgroupOf H N := by
  obtain ⟨i, hi⟩ := h
  exact factor_group_through_subgroup N H.inclusion i hi

private theorem subgroup_of_intersection {G : GroupScheme k}
    {family : Set (ClosedSubgroup G)} {I H : ClosedSubgroup G}
    (hI : IsSchemeIntersection family I) :
    IsSubgroupOf H I ↔ ∀ B ∈ family, IsSubgroupOf H B := by
  constructor
  · intro h B hB
    exact subgroup_of_sections ((hI _ _).mp
      (sections_of_subgroup h (inclusion_mem_sections H)) B hB)
  · intro h
    apply subgroup_of_sections ((hI _ _).mpr ?_)
    intro B hB
    exact sections_of_subgroup (h B hB) (inclusion_mem_sections H)

private theorem subgroup_of_reduced_component [PerfectField k] {G : AffineAlgebraicGroup k}
    {I H : ClosedSubgroup G.val}
    (C : EquivariantUnipotentSeries.ReducedIdentityComponent (closedSubgroupAlgebraicGroup I))
    (hs : Smooth H.group.X.hom) (hc : ConnectedSpace H.group.X.left)
    (h : IsSubgroupOf H I) : IsSubgroupOf H (subgroupOfSubgroup I C.subgroup) := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hg⟩ := ReducedIdentityComponent.factorHom C (A := closedSubgroupAlgebraicGroup H) f hs hc
  exact ⟨g, by
    change g ≫ C.subgroup.inclusion ≫ I.inclusion = H.inclusion
    rw [← Category.assoc, hg, hf]⟩

private theorem factors_through_closed_of_rational_points [IsAlgClosed k]
    {X Y Z : SchemeOver k} [IsReduced X.left] [LocallyOfFiniteType X.hom]
    (i : Y ⟶ Z) (hi : IsClosedImmersion i.left) (f : X ⟶ Z)
    (h : ∀ a : 𝟙_ (SchemeOver k) ⟶ X, ∃ b : 𝟙_ (SchemeOver k) ⟶ Y, b ≫ i = a ≫ f) :
    ∃ r : X ⟶ Y, r ≫ i = f := by
  let q := pullback.fst f.left i.left
  letI : IsClosedImmersion q := inferInstanceAs (IsClosedImmersion (pullback.fst f.left i.left))
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hclosed : closedPoints X.left ⊆ Set.range q := by
    intro x hx
    let a := sectionOfClosedPoint X x hx
    obtain ⟨b, hb⟩ := h a
    let p := pullback.lift a.left b.left
      (congrArg (fun w : 𝟙_ (SchemeOver k) ⟶ Z ↦ w.left) hb.symm)
    refine ⟨p (IsLocalRing.closedPoint k), ?_⟩
    rw [← Scheme.Hom.comp_apply]
    exact (congrArg (fun g : Spec (CommRingCat.of k) ⟶ X.left ↦
      g (IsLocalRing.closedPoint k)) (pullback.lift_fst _ _ _)).trans
        (sectionOfClosedPoint_apply X x hx)
  have hall := q.isClosedEmbedding.isClosed_range.closure_subset_iff.mpr hclosed
  rw [closure_closedPoints] at hall
  letI : Surjective q := ⟨fun x ↦ hall (Set.mem_univ x)⟩
  letI : IsIso q := isIso_of_isClosedImmersion_of_surjective q
  let r := inv q ≫ pullback.snd f.left i.left
  have hr : r ≫ i.left = f.left := by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  exact ⟨Over.homMk r (by rw [← Over.w i, ← Category.assoc, hr, Over.w f]),
    Over.OverMorphism.ext hr⟩

private theorem normal_of_rational_conjugation [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (hgs : Smooth G.val.X.hom) (H : ClosedSubgroup G.val) (hhs : Smooth H.group.X.hom)
    (h : ∀ g : 𝟙_ (SchemeOver k) ⟶ G.val.X, IsSubgroupOf (conjugate g H) H) :
    IsNormalSubgroup H.inclusion := by
  let X := G.val.X ⊗ H.group.X
  letI := hgs
  letI := hhs
  haveI : Smooth X.hom := by
    change Smooth (pullback.fst G.val.X.hom H.group.X.hom ≫ G.val.X.hom)
    infer_instance
  haveI : IsReduced X.left := isReduced_of_smooth_over_field X.hom
  apply factors_through_closed_of_rational_points H.inclusion.hom.hom H.isClosedImmersion
    (subgroupConjugation H.inclusion)
  intro p
  let g := p ≫ fst G.val.X H.group.X
  let v := p ≫ snd G.val.X H.group.X
  obtain ⟨j, hj⟩ := h g
  refine ⟨v ≫ j.hom.hom, ?_⟩
  have he := congrArg (Grp.forget (SchemeOver k)).map hj
  change j.hom.hom ≫ H.inclusion.hom.hom =
    H.inclusion.hom.hom ≫ (conjugation g).hom.hom at he
  have hunit : toUnit (𝟙_ (SchemeOver k)) = 𝟙 (𝟙_ (SchemeOver k)) :=
    (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
  rw [Category.assoc, he, ← Category.assoc, conjugation_apply, hunit, Category.id_comp]
  simp only [subgroupConjugation, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc, g, v]

private theorem conjugate_le_of_normal {G : GroupScheme k} {H : ClosedSubgroup G}
    (h : IsNormalSubgroup H.inclusion) (g : 𝟙_ (SchemeOver k) ⟶ G.X) :
    IsSubgroupOf (conjugate g H) H := by
  apply subgroup_of_sections
  change ∃ v : H.group.X ⟶ H.group.X, v ≫ H.inclusion.hom.hom =
    H.inclusion.hom.hom ≫ (conjugation g).hom.hom
  rw [conjugation_apply]
  simpa only [Category.id_comp] using
    (normalSubgroup_conjugate_sections h (toUnit H.group.X ≫ g) (𝟙 H.group.X))

private theorem normal_solvable_in_borel [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    {H B : ClosedSubgroup G.val} (hH : IsSmoothConnectedNormal H) (hsol : IsSolvable H.group)
    (hB : IsBorel B) : IsSubgroupOf H B := by
  obtain ⟨A, hA, hHA⟩ := exists_borel_above G H ⟨hH.1, hH.2.1, hsol⟩
  obtain ⟨g, e, he⟩ := LinearAlgebraicGroups.GeometricBorelConjugacy.borelsConjugate G hs hc A B hA hB
  have hAB : IsSubgroupOf (conjugate g A) B := by
    refine ⟨e.hom, Grp.hom_ext _ _ ?_⟩
    exact he.trans (conjugation_apply g A.inclusion.hom.hom).symm
  have hHH := conjugate_subgroupOf g (conjugate_le_of_normal hH.2.2 g⁻¹)
  have heq := conjugate_inv_cancel g⁻¹ H
  rw [inv_inv] at heq
  rw [heq] at hHH
  exact subgroupOf_trans hHH (subgroupOf_trans (conjugate_subgroupOf g hHA) hAB)

private theorem solvable_of_smooth_subgroup [IsAlgClosed k] {G : AffineAlgebraicGroup k}
    {H B : ClosedSubgroup G.val} (hs : Smooth H.group.X.hom)
    (hc : ConnectedSpace H.group.X.left) (hB : IsSmoothConnectedSolvable B)
    (hHB : IsSubgroupOf H B) : IsSolvable H.group := by
  obtain ⟨f, hf⟩ := hHB
  letI : IsClosedImmersion f.hom.hom.left := factor_closed hf
  letI : Mono f.hom.hom := Over.mono_of_mono_left _
  letI : Group.IsSolvable (𝟙_ (SchemeOver k) ⟶ B.group.X) :=
    (solvable_iff_sections (closedSubgroupAlgebraicGroup B) hB.1 hB.2.1).mp hB.2.2
  exact (solvable_iff_sections (closedSubgroupAlgebraicGroup H) hs hc).mpr
    (Group.isSolvable_of_isSolvable_injective (f := rationalMap f) fun _ _ h ↦
      (cancel_mono f.hom.hom).mp h)

private theorem exists_solvableRadical_intersection [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left) :
    ∃ (I : ClosedSubgroup G.val)
      (J : EquivariantUnipotentSeries.ReducedIdentityComponent (closedSubgroupAlgebraicGroup I)),
      IsSchemeIntersection {B | IsBorel B} I ∧ IsSolvableRadical G (subgroupOfSubgroup I J.subgroup) := by
  obtain ⟨I, hI⟩ := schemeIntersection_exists G {B | IsBorel B}
  obtain ⟨J⟩ := EquivariantUnipotentSeries.exists_smooth_identity_component
    (closedSubgroupAlgebraicGroup I)
  let H := subgroupOfSubgroup I J.subgroup
  have hHI : IsSubgroupOf H I := ⟨J.subgroup.inclusion, rfl⟩
  have hB (B : ClosedSubgroup G.val) (hB : IsBorel B) : IsSubgroupOf H B :=
    (subgroup_of_intersection hI).mp hHI B hB
  have hnorm : IsNormalSubgroup H.inclusion := by
    apply normal_of_rational_conjugation G hs H J.smooth
    intro g
    apply subgroup_of_reduced_component J J.smooth J.connected
    apply (subgroup_of_intersection hI).mpr
    intro B hBor
    have h := conjugate_subgroupOf g (hB (conjugate g⁻¹ B) (borel_conjugate g⁻¹ hBor))
    have heq := conjugate_inv_cancel g⁻¹ B
    rw [inv_inv] at heq
    rwa [heq] at h
  obtain ⟨B, hBor⟩ := LinearAlgebraicGroups.GeometricBorelConjugacy.borelExists G hs hc
  have hsol := solvable_of_smooth_subgroup (H := H) J.smooth J.connected hBor.1 (hB B hBor)
  refine ⟨I, J, hI, ⟨J.smooth, J.connected, hnorm⟩, hsol, ?_⟩
  intro N hN hn
  apply subgroup_of_reduced_component J hN.1 hN.2.1
  exact (subgroup_of_intersection hI).mpr (fun B hBor ↦ normal_solvable_in_borel G hs hc hN hn hBor)

theorem solvableRadicalFromBorelIntersection_conditional
    (_ : BorelQuotientFixedPoints.{u}) (_ : NormalTorusCentral.{u}) (_ : QuotientByCentralizer.{u}) :
    SolvableRadicalFromBorelIntersection.{u} := by
  intro k _ _ G hs hc
  obtain ⟨I, J, hI, hJ⟩ := exists_solvableRadical_intersection G hs hc
  exact ⟨I, J.subgroup, hI, reducedComponent_spec J, hJ⟩

open private radicalQuotient from LinearAlgebraicGroups.Solvable.GeometricTorusSplitting

private theorem unipotent_of_subgroup {G : AffineAlgebraicGroup k}
    {H B : ClosedSubgroup G.val} (hHB : IsSubgroupOf H B)
    (hB : IsUnipotent (closedSubgroupAlgebraicGroup B)) :
    IsUnipotent (closedSubgroupAlgebraicGroup H) := by
  obtain ⟨f, hf⟩ := hHB
  let H' : ClosedSubgroup B.group := ⟨H.group, f, factor_closed hf⟩
  exact Unipotent.closedSubgroupsUnipotent (closedSubgroupAlgebraicGroup B) H' hB

private theorem unipotent_solvable [IsAlgClosed k] (U : AffineAlgebraicGroup k)
    (hs : Smooth U.val.X.hom) (hc : ConnectedSpace U.val.X.left) (hu : IsUnipotent U) :
    IsSolvable U.val := by
  obtain ⟨_, S, _, _, hS⟩ := Unipotent.perfectFieldSplitness U hs hc hu
  have hsplit := splitSolvable_of_additiveSeries S hS (Iso.refl U.val)
  letI := split_solvable_points hsplit (CommAlgCat.of k k)
  let e := (affineBaseTerminal k).uniqueUpToIso (isTerminalTensorUnit (C := SchemeOver k))
  let f : ((𝟙_ (SchemeOver k)) ⟶ U.val.X) →* Points U.val.X (CommAlgCat.of k k) :=
    { toFun := fun a ↦ e.hom ≫ a
      map_one' := MonObj.comp_one _
      map_mul' _ _ := MonObj.comp_mul _ _ _ }
  exact (solvable_iff_sections U hs hc).mpr
    (Group.isSolvable_of_isSolvable_injective (f := f) fun _ _ h ↦ (cancel_epi e.hom).mp h)

private theorem normal_unipotent_in_borel_radical [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    {N B : ClosedSubgroup G.val} {U : ClosedSubgroup B.group}
    (hN : IsSmoothConnectedNormal N) (hn : IsUnipotent (closedSubgroupAlgebraicGroup N))
    (hB : IsBorel B) (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U) :
    IsSubgroupOf N (subgroupOfSubgroup B U) := by
  obtain ⟨f, hf⟩ := normal_solvable_in_borel G hs hc hN
    (unipotent_solvable (closedSubgroupAlgebraicGroup N) hN.1 hN.2.1 hn) hB
  let N' : ClosedSubgroup B.group := ⟨N.group, f, factor_closed hf⟩
  obtain ⟨j, hj⟩ := hU.2.2 N' ⟨hN.1, hN.2.1, factor_normal hN.2.2 hf⟩ hn
  exact ⟨j, by
    change j ≫ U.inclusion ≫ B.inclusion = N.inclusion
    rw [← Category.assoc, hj]
    exact hf⟩

private theorem unipotentRadical_of_solvableRadical [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) (hs : Smooth G.val.X.hom)
    (S : ClosedSubgroup G.val) (hS : IsSolvableRadical G S) :
    ∃ U : ClosedSubgroup S.group, IsUnipotentRadical G (subgroupOfSubgroup S U) ∧
      ∀ H : ClosedSubgroup G.val, IsSubgroupOf H S →
        IsUnipotent (closedSubgroupAlgebraicGroup H) → IsSubgroupOf H (subgroupOfSubgroup S U) := by
  obtain ⟨U, _, _, hU, _, _⟩ := radicalQuotient (closedSubgroupAlgebraicGroup S) hS.1.1 hS.1.2.1 hS.2.1
  let N := subgroupOfSubgroup S U
  have hNS : IsSubgroupOf N S := ⟨U.inclusion, rfl⟩
  have hmax (H : ClosedSubgroup G.val) (hHS : IsSubgroupOf H S)
      (hH : IsUnipotent (closedSubgroupAlgebraicGroup H)) : IsSubgroupOf H N := by
    obtain ⟨j, hj⟩ := hHS
    let V : ClosedSubgroup S.group := ⟨H.group, j, factor_closed hj⟩
    obtain ⟨l, hl⟩ := hU.2.2.2.2 V hH
    exact ⟨l, by
      change l ≫ U.inclusion ≫ S.inclusion = H.inclusion
      rw [← Category.assoc, hl]
      exact hj⟩
  have hnorm : IsNormalSubgroup N.inclusion := by
    apply normal_of_rational_conjugation G hs N hU.1
    intro g
    apply hmax (conjugate g N) _ hU.2.2.2.1
    exact subgroupOf_trans (conjugate_subgroupOf g hNS) (conjugate_le_of_normal hS.1.2.2 g)
  refine ⟨U, ⟨⟨hU.1, hU.2.1, hnorm⟩, hU.2.2.2.1, ?_⟩, hmax⟩
  intro H hH hh
  exact hmax H (hS.2.2 H hH
    (unipotent_solvable (closedSubgroupAlgebraicGroup H) hH.1 hH.2.1 hh)) hh

private theorem unipotentIntersection_of_borel_containment [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (T : ClosedSubgroup G.val) (hT : IsMaximalTorus T)
    (hcore : ∀ H : ClosedSubgroup G.val, Smooth H.group.X.hom → ConnectedSpace H.group.X.left →
      IsUnipotent (closedSubgroupAlgebraicGroup H) →
        (∀ K ∈ borelUnipotentRadicals T, IsSubgroupOf H K) →
        ∀ B : ClosedSubgroup G.val, IsBorel B → IsSubgroupOf H B) :
    ∃ (I : ClosedSubgroup G.val) (J : ClosedSubgroup I.group),
      IsSchemeIntersection (borelUnipotentRadicals T) I ∧ IsReducedIdentityComponent J ∧
        IsUnipotentRadical G (subgroupOfSubgroup I J) := by
  obtain ⟨I, hI⟩ := schemeIntersection_exists G (borelUnipotentRadicals T)
  obtain ⟨J⟩ := EquivariantUnipotentSeries.exists_smooth_identity_component
    (closedSubgroupAlgebraicGroup I)
  let H := subgroupOfSubgroup I J.subgroup
  have hHI : IsSubgroupOf H I := ⟨J.subgroup.inclusion, rfl⟩
  have hHB := (subgroup_of_intersection hI).mp hHI
  have hmax (N : ClosedSubgroup G.val) (hN : IsSmoothConnectedNormal N)
      (hn : IsUnipotent (closedSubgroupAlgebraicGroup N)) : IsSubgroupOf N H := by
    apply subgroup_of_reduced_component J hN.1 hN.2.1
    apply (subgroup_of_intersection hI).mpr
    rintro _ ⟨B, U, hB, _, hU, rfl⟩
    exact normal_unipotent_in_borel_radical G hs hc hN hn hB hU
  obtain ⟨B, hBor, hTB⟩ :=
    LinearAlgebraicGroups.GeometricBorelConjugacy.torusContainedInBorel G hs hc T hT.1
  obtain ⟨V, _, _, hV, _, _⟩ :=
    radicalQuotient (closedSubgroupAlgebraicGroup B) hBor.1.1 hBor.1.2.1 hBor.1.2.2
  have hVR : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) V :=
    ⟨⟨hV.1, hV.2.1, hV.2.2.1⟩, hV.2.2.2.1, fun W _ hw ↦ hV.2.2.2.2 W hw⟩
  have hH : IsUnipotent (closedSubgroupAlgebraicGroup H) :=
    unipotent_of_subgroup (hHB _ ⟨B, V, hBor, hTB, hVR, rfl⟩) hVR.2.1
  obtain ⟨L, M, hL, hS⟩ := exists_solvableRadical_intersection G hs hc
  let S := subgroupOfSubgroup L M.subgroup
  have hHS : IsSubgroupOf H S := by
    apply subgroup_of_reduced_component M J.smooth J.connected
    exact (subgroup_of_intersection hL).mpr (hcore H J.smooth J.connected hH hHB)
  obtain ⟨U, hR, hRmax⟩ := unipotentRadical_of_solvableRadical G hs S hS
  have hHR := hRmax H hHS hH
  have hRH := hmax _ hR.1 hR.2.1
  refine ⟨I, J.subgroup, hI, reducedComponent_spec J, ⟨J.smooth, J.connected, ?_⟩, hH, hmax⟩
  apply normal_of_rational_conjugation G hs H J.smooth
  intro g
  exact subgroupOf_trans (conjugate_subgroupOf g hHR)
    (subgroupOf_trans (conjugate_le_of_normal hR.1.2.2 g) hRH)


open WithConv
open scoped TensorProduct

open RightComodule
open Specs.Unipotent (HasInvariantVectors)
open RationalRepresentations (invariants invariantDifference invariantDifference_apply)

private theorem regularSubcomodule_contains_one
    (A : HopfAlgebraCategory k) (hA : HasInvariantVectors A)
    (W : Submodule k A) (hW : (RightComodule.regular (k := k) (C := A)).IsSubcomodule W)
    {a : A} (ha : a ∈ W) (hne : a ≠ 0) : (1 : A) ∈ W := by
  let ρ := RightComodule.regular (k := k) (C := A)
  obtain ⟨σ, hσ⟩ := (RightComodule.isSubcomodule_iff_exists_coaction ρ W).mp hW
  let x : W := ⟨a, ha⟩
  obtain ⟨F, hx⟩ := σ.exists_finiteSubcomodule x
  letI := F.property.2
  have hn : (⟨x, hx⟩ : F.val) ≠ 0 := by
    intro h
    exact hne (congrArg (fun v : F.val ↦ v.val.val) h)
  letI : Nontrivial F.val := ⟨⟨⟨x, hx⟩, 0, hn⟩⟩
  obtain ⟨τ, hτ⟩ := (RightComodule.isSubcomodule_iff_exists_coaction σ F.val).mp F.property.1
  obtain ⟨v, hv, hinv⟩ := hA F.val τ
  have hi : τ.coaction v = v ⊗ₜ[k] (1 : A) := by
    simpa only [invariants, LinearMap.mem_ker, invariantDifference_apply, sub_eq_zero] using hinv
  have hvF : σ.coaction v.val = v.val ⊗ₜ[k] (1 : A) := by
    have he := (DFunLike.congr_fun hτ v).symm
    change σ.coaction v.val = (F.val.subtype.rTensor A) (τ.coaction v) at he
    rw [he, hi, LinearMap.rTensor_tmul]
    rfl
  let b : A := v.val.val
  have hb : Coalgebra.comul (R := k) b = b ⊗ₜ[k] (1 : A) := by
    have he := (DFunLike.congr_fun hσ v.val).symm
    change Coalgebra.comul (R := k) b = (W.subtype.rTensor A) (σ.coaction v.val) at he
    rw [he, hvF, LinearMap.rTensor_tmul]
    rfl
  have he : b = Coalgebra.counit (R := k) b • (1 : A) := by
    have h := congrArg (fun t : A ⊗[k] A ↦ (TensorProduct.lid k A)
      ((Coalgebra.counit (R := k)).rTensor A t)) hb
    simpa only [Coalgebra.rTensor_counit_comul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
      one_smul] using h
  have hbn : b ≠ 0 := fun h ↦ hv (Subtype.ext (Subtype.ext h))
  have hc : Coalgebra.counit (R := k) b ≠ 0 := by
    intro h
    apply hbn
    rw [he, h, zero_smul]
  let c := Coalgebra.counit (R := k) b
  have hcb : c • (1 : A) ∈ W := he ▸ v.val.property
  have h := W.smul_mem c⁻¹ hcb
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h

private abbrev rightEvaluation (A : HopfAlgebraCategory k) (g : A →ₐ[k] k) : A →ₗ[k] A :=
  (TensorProduct.rid k A).toLinearMap.comp
    ((g.toLinearMap.lTensor A).comp (Coalgebra.comul (R := k)))

private theorem rightEvaluation_apply (A : HopfAlgebraCategory k) (g h : A →ₐ[k] k) (a : A) :
    h (rightEvaluation A g a) = (toConv h * toConv g) a := by
  rw [AlgHom.convMul_apply]
  change h (TensorProduct.rid k A (g.toLinearMap.lTensor A (Coalgebra.comul (R := k) a))) = _
  generalize Coalgebra.comul (R := k) a = t
  induction t with
  | tmul x y => simp [mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

open private eq_zero_of_algHom_eq_zero tensorCoordinate_evaluation
  from LinearAlgebraicGroups.Affine.RationalRepresentations

private theorem regularSubcomodule_of_stable [IsAlgClosed k]
    (A : HopfAlgebraCategory k) [Algebra.FiniteType k A] [IsReduced A]
    (W : Submodule k A) (hW : ∀ (g : A →ₐ[k] k) (a : A), a ∈ W →
      rightEvaluation A g a ∈ W) :
    (RightComodule.regular (k := k) (C := A)).IsSubcomodule W := by
  intro x
  have hex := rTensor_exact A (LinearMap.exact_subtype_mkQ W) W.mkQ_surjective
  rw [← hex.linearMap_ker_eq, LinearMap.mem_ker]
  let b := Module.Basis.ofVectorSpace k (A ⧸ W)
  let t := W.mkQ.rTensor A (Coalgebra.comul (R := k) x.val)
  change t = 0
  have ht (g : A →ₐ[k] k) : g.toLinearMap.lTensor (A ⧸ W) t = 0 := by
    have he (s : A ⊗[k] A) :
        TensorProduct.rid k (A ⧸ W) (g.toLinearMap.lTensor (A ⧸ W) (W.mkQ.rTensor A s)) =
        W.mkQ (TensorProduct.rid k A (g.toLinearMap.lTensor A s)) := by
      induction s <;> simp_all
    apply (TensorProduct.rid k (A ⧸ W)).injective
    rw [map_zero]
    rw [show TensorProduct.rid k (A ⧸ W) (g.toLinearMap.lTensor (A ⧸ W) t) =
      W.mkQ (rightEvaluation A g x.val) from he _]
    exact (Submodule.Quotient.mk_eq_zero W).mpr (hW g x.val x.property)
  classical
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  ext i
  rw [map_zero, Finsupp.zero_apply, TensorProduct.equivFinsuppOfBasisLeft_apply]
  change RationalRepresentations.tensorCoordinate b i t = 0
  apply eq_zero_of_algHom_eq_zero (F := k)
  intro g
  change g.toLinearMap (RationalRepresentations.tensorCoordinate b i t) = _
  rw [← tensorCoordinate_evaluation b g.toLinearMap, ht g, map_zero]

private theorem affineBoundary_empty [IsAlgClosed k]
    (A : HopfAlgebraCategory k) [Algebra.FiniteType k A] [IsReduced A]
    (hinv : HasInvariantVectors A) {B : Type u} [CommRing B] [Algebra k B]
    (j : B →ₐ[k] A) (hj : Function.Injective j) (I : Ideal B)
    (hstable : ∀ g : A →ₐ[k] k, ∃ t : B →ₐ[k] B,
      Set.MapsTo t I I ∧ ∀ h : A →ₐ[k] k,
        h.comp (j.comp t) = (toConv h * toConv g).ofConv.comp j)
    (hne : I ≠ ⊥) : (1 : B) ∈ I := by
  let W := (I.restrictScalars k).map j.toLinearMap
  have hW : (RightComodule.regular (k := k) (C := A)).IsSubcomodule W := by
    apply regularSubcomodule_of_stable
    intro g a ha
    change a ∈ (I.restrictScalars k).map j.toLinearMap at ha
    obtain ⟨b, hb, rfl⟩ := ha
    obtain ⟨t, ht, he⟩ := hstable g
    refine ⟨t b, ht hb, ?_⟩
    change j (t b) = rightEvaluation A g (j b)
    apply sub_eq_zero.mp
    apply eq_zero_of_algHom_eq_zero (F := k)
    intro h
    rw [map_sub, sub_eq_zero, rightEvaluation_apply]
    exact DFunLike.congr_fun (he h) b
  have hex : ∃ b : B, b ∈ I ∧ b ≠ 0 := by
    by_contra! h
    exact hne (bot_unique fun x hx ↦ Ideal.mem_bot.mpr (h x hx))
  obtain ⟨b, hb, hbn⟩ := hex
  have h1 := regularSubcomodule_contains_one A hinv W hW
    (show j b ∈ W from ⟨b, hb, rfl⟩) (fun h ↦ hbn (hj (h.trans (map_zero j).symm)))
  obtain ⟨c, hc, he⟩ := h1
  have he' : j c = j 1 := he.trans (map_one j).symm
  exact hj he' ▸ hc

open WithConv
open private toClosure toClosure_fac toImage_dominant orbitClosure_action orbitMap_comp mono_over
  from LinearAlgebraicGroups.Flag.SmoothOrbit
open Specs.SmoothOrbit (orbitMap orbitClosure orbitSet closureInclusion)

private abbrev affineScheme (B : CommAlgCat k) : SchemeOver k :=
  (algSpec (CommRingCat.of k)).obj (op B)

private def affineCoordinates {B D : CommAlgCat k}
    (f : affineScheme D ⟶ affineScheme B) : B →ₐ[k] D :=
  (((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage f).unop).hom

private theorem affineCoordinates_spec {B D : CommAlgCat k}
    (f : affineScheme D ⟶ affineScheme B) :
    f.left = Spec.map (CommRingCat.ofHom (affineCoordinates f).toRingHom) :=
  congrArg (fun f : affineScheme D ⟶ affineScheme B ↦ f.left)
    ((algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage f).symm

private theorem affineCoordinates_injective {B D : CommAlgCat k}
    (f : affineScheme D ⟶ affineScheme B) [IsSchemeTheoreticallyDominant f.left]
    [QuasiCompact f.left] : Function.Injective (affineCoordinates f) := by
  have h := f.left.app_injective ⊤
  intro x y hxy
  let e := Scheme.ΓSpecIso (CommRingCat.of B)
  let e' := Scheme.ΓSpecIso (CommRingCat.of D)
  suffices e.inv x = e.inv y from (ConcreteCategory.bijective_of_isIso e.inv).1 this
  apply h
  apply (ConcreteCategory.bijective_of_isIso e'.hom).1
  have he := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (affineCoordinates f).toRingHom)
  -- Use naturality of the global sections isomorphisms on the affine map.
  rw [← affineCoordinates_spec f] at he
  change f.left.appTop ≫ e'.hom = e.hom ≫ CommRingCat.ofHom
    (affineCoordinates f).toRingHom at he
  have h' (a : B) : e'.hom (f.left.appTop (e.inv a)) = affineCoordinates f a := by
    have ha := ConcreteCategory.congr_hom he (e.inv a)
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at ha
    have he' : e.hom (e.inv a) = a := ConcreteCategory.congr_hom e.inv_hom_id a
    exact ha.trans (congrArg (affineCoordinates f) he')
  exact (h' x).trans (hxy.trans (h' y).symm)

private def rationalSpecMap : 𝟙_ (SchemeOver k) ⟶ affineScheme (CommAlgCat.of k k) :=
  Over.homMk (𝟙 (Spec (CommRingCat.of k))) (by
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _
    rw [Category.id_comp, show CommRingCat.ofHom (algebraMap k k) = 𝟙 _ from rfl,
      Spec.map_id])

private abbrev specPoint (A : HopfAlgebraCategory k) (g : A →ₐ[k] k) :
    𝟙_ (SchemeOver k) ⟶ (specGroup A).X :=
  rationalSpecMap ≫ (Spec.mapMulEquiv (R := k) (S := A) (T := k)) (toConv g)

private theorem specPoint_mul (A : HopfAlgebraCategory k) (g h : A →ₐ[k] k) :
    specPoint A (toConv g * toConv h).ofConv = specPoint A g * specPoint A h := by
  simp only [specPoint, WithConv.toConv_ofConv, map_mul, MonObj.comp_mul]

private theorem specPoint_left (A : HopfAlgebraCategory k) (g : A →ₐ[k] k) :
    (specPoint A g).left = Spec.map (CommRingCat.ofHom g.toRingHom) := by
  change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom g.toRingHom) = _
  exact Category.id_comp _

private theorem rightOrbitEquation {G : GroupScheme k} {X : SchemeOver k}
    (a : ModObj G.X X) (x : 𝟙_ (SchemeOver k) ⟶ X)
    (g h : 𝟙_ (SchemeOver k) ⟶ G.X) :
    letI := a
    (h * g)⁻¹ ≫ orbitMap a x = g⁻¹ • (h⁻¹ ≫ orbitMap a x) := by
  letI := a
  rw [mul_inv_rev, orbitMap_comp, mul_smul, ← orbitMap_comp]

private theorem rationalTranslation_preserves_boundary {G : GroupScheme k} {X Y : SchemeOver k}
    (a : ModObj G.X X) (b : ModObj G.X Y)
    {q : G.X ⟶ Y} {i : Y ⟶ X} [Mono i] (x : 𝟙_ (SchemeOver k) ⟶ X)
    (hq : q ≫ i = orbitMap a x)
    (hi : b.smul ≫ i = (𝟙 G.X ⊗ₘ i) ≫ a.smul)
    (g : 𝟙_ (SchemeOver k) ⟶ G.X) :
    letI := b
    let t : Y ⟶ Y := (toUnit Y ≫ g) • (𝟙 Y)
    Set.MapsTo t.left (Set.range q.left)ᶜ (Set.range q.left)ᶜ := by
  letI := b
  let t : Y ⟶ Y := (toUnit Y ≫ g) • (𝟙 Y)
  let s : Y ⟶ Y := (toUnit Y ≫ g⁻¹) • (𝟙 Y)
  have hs (p : Y.left) : s.left (t.left p) = p := by
    have he : t ≫ s = 𝟙 Y := by
      change t ≫ ((toUnit Y ≫ g⁻¹) • (𝟙 Y)) = _
      rw [ModObj.comp_smul, comp_toUnit_assoc, Category.comp_id]
      change (toUnit Y ≫ g⁻¹) • ((toUnit Y ≫ g) • (𝟙 Y)) = _
      rw [GrpObj.comp_inv, inv_smul_smul]
    exact congrArg (fun f : Y ⟶ Y ↦ f.left p) he
  have he : q ≫ s = ((toUnit G.X ≫ g⁻¹) * (𝟙 G.X)) ≫ q := by
    apply (cancel_mono i).mp
    rw [Category.assoc, Category.assoc, hq]
    change q ≫ lift (toUnit Y ≫ g⁻¹) (𝟙 Y) ≫ b.smul ≫ i =
      ((toUnit G.X ≫ g⁻¹) * (𝟙 G.X)) ≫ orbitMap a x
    rw [hi, comp_lift_assoc, Category.comp_id, comp_toUnit_assoc, lift_map_assoc,
      Category.comp_id, hq]
    letI := a
    change (toUnit G.X ≫ g⁻¹) • orbitMap a x = _
    rw [orbitMap_comp, mul_smul, ← orbitMap_comp, Category.id_comp]
  change Set.MapsTo t.left (Set.range q.left)ᶜ (Set.range q.left)ᶜ
  intro p hp ht
  obtain ⟨z, hz⟩ := ht
  refine hp ⟨(((toUnit G.X ≫ g⁻¹) * (𝟙 G.X)).left z), ?_⟩
  have ee := congrArg (fun f : G.X ⟶ Y ↦ f.left z) he
  change s.left (q.left z) = _ at ee
  rw [hz, hs] at ee
  exact ee.symm

private theorem orbitClosure_isClosed [IsAlgClosed k]
    (U : AffineAlgebraicGroup k) (X : SchemeOver k) (a : ModObj U.val.X X)
    (hs : Smooth U.val.X.hom) (hu : IsUnipotent U)
    [IsAffine X.left] [LocallyOfFiniteType X.hom]
    (x : 𝟙_ (SchemeOver k) ⟶ X) : IsClosed (orbitSet a x) := by
  letI := U.property.1
  letI := hs
  haveI : IsAffineHom X.hom := isAffineHom_of_isAffine X.hom
  obtain ⟨P⟩ := SmoothOrbit.schemeOrbit k U X a x hs inferInstance inferInstance inferInstance
  let Z := orbitClosure a x
  let q := toClosure a x
  let i := closureInclusion a x
  letI : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion (orbitMap a x).left.imageι)
  letI : Mono i := mono_over i
  letI : IsAffine Z.left := (IsClosedImmersion.isAffine_surjective_of_isAffine i.left).1
  have hq : q ≫ i = orbitMap a x := toClosure_fac a x
  haveI : IsAffineHom (orbitMap a x).left := IsAffineHom.of_comp _ X.hom
  haveI : IsSchemeTheoreticallyDominant q.left := toImage_dominant (orbitMap a x).left
  obtain ⟨b, hb, hbi⟩ := orbitClosure_action a x
  letI := b
  have hrange : Set.range q.left = Set.range P.openInClosure.left := by
    have h := P.factors
    change P.projection.left ≫ P.openInClosure.left = q.left at h
    rw [← h]
    haveI := P.surjective
    exact P.projection.left.surjective.range_comp _
  have hopen : IsOpen (Set.range q.left) := by
    rw [hrange]
    letI := P.isOpen
    exact P.openInClosure.left.isOpenEmbedding.isOpen_range
  suffices hfull : Set.range q.left = Set.univ by
    change IsClosed (Set.range (orbitMap a x).left)
    rw [← hq, Over.comp_left]
    change IsClosed (Set.range (⇑i.left ∘ ⇑q.left))
    rw [Set.range_comp, hfull, Set.image_univ]
    exact i.left.isClosedEmbedding.isClosed_range
  by_contra hn
  obtain ⟨A, ⟨e⟩, hinv⟩ := hu
  let E : (specGroup A).X ≅ U.val.X := (Grp.forget (SchemeOver k)).mapIso e
  obtain ⟨B', ⟨eZ⟩⟩ := essImage_algSpec.mpr ‹IsAffine Z.left›
  let B : CommAlgCat k := B'.unop
  let EZ : affineScheme B ≅ Z := eZ
  let f : (specGroup A).X ⟶ affineScheme B := E.hom ≫ ι[U.val.X] ≫ q ≫ EZ.inv
  let r : B →ₐ[k] A := affineCoordinates f
  let K : Set (PrimeSpectrum B) := EZ.hom.left ⁻¹' (Set.range q.left)ᶜ
  have hc : IsClosed K := hopen.isClosed_compl.preimage EZ.hom.left.continuous
  obtain ⟨I, hIr, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_radical_ideal K).mp hc
  have hne : I ≠ ⊥ := by
    intro h
    obtain ⟨z, hz⟩ := EZ.hom.left.surjective (q.left
      (η[U.val.X].left (IsLocalRing.closedPoint k)))
    have hu : K = Set.univ := by rw [hI, h]; simp
    have hmem : z ∈ K := hu ▸ Set.mem_univ _
    exact hmem ⟨_, hz.symm⟩
  have hproper : (1 : B) ∉ I := by
    obtain ⟨z, hz⟩ := Set.nonempty_compl.mpr hn
    obtain ⟨p, hp⟩ := EZ.hom.left.surjective z
    have hm : p ∈ K := by simpa only [K, Set.mem_preimage, hp] using hz
    rw [hI] at hm
    intro h
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (hm h) isUnit_one)
  have hSA : Smooth ((specGroup A).X.hom) := by
    rw [← Over.w E.hom]
    infer_instance
  have hred : IsReduced (specGroup A).X.left := by
    letI := hSA
    exact isReduced_of_smooth_over_field (specGroup A).X.hom
  haveI : IsReduced A := (affine_isReduced_iff (CommRingCat.of A)).mp hred
  have hft : LocallyOfFiniteType (specGroup A).X.hom := by
    letI := U.property.2.1
    rw [← Over.w E.hom]
    infer_instance
  haveI : Algebra.FiniteType k A := (hopfSpec_locallyOfFiniteType_iff k A).mp hft
  haveI : IsIso E.hom.left := (Over.forget _).map_isIso E.hom
  haveI : IsIso EZ.inv.left := (Over.forget _).map_isIso EZ.inv
  haveI : IsIso ι[U.val.X].left := (Over.forget _).map_isIso ι[U.val.X]
  haveI : IsSchemeTheoreticallyDominant f.left := by
    dsimp [f]
    infer_instance
  haveI : IsAffine (specGroup A).X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  haveI : IsAffine (affineScheme B).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of B)))
  haveI : IsAffineHom f.left := isAffineHom_of_isAffine f.left
  haveI : QuasiCompact f.left := inferInstance
  apply hproper
  apply affineBoundary_empty A hinv r (affineCoordinates_injective f) I ?_ hne
  intro g
  let gU : 𝟙_ (SchemeOver k) ⟶ U.val.X := specPoint A g ≫ E.hom
  let t : Z ⟶ Z := (toUnit Z ≫ gU⁻¹) • (𝟙 Z)
  let m : affineScheme B ⟶ affineScheme B := EZ.hom ≫ t ≫ EZ.inv
  let d := affineCoordinates m
  have hmap := rationalTranslation_preserves_boundary a b x hq hbi gU⁻¹
  refine ⟨d, ?_, ?_⟩
  · intro s hs
    have he : I = PrimeSpectrum.vanishingIdeal K := by
      rw [hI, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
      exact hIr.radical.symm
    have hs' := (PrimeSpectrum.mem_vanishingIdeal K s).mp (he ▸ hs)
    suffices h : d s ∈ PrimeSpectrum.vanishingIdeal K from he.symm ▸ h
    refine (PrimeSpectrum.mem_vanishingIdeal K (d s)).mpr (fun p hp ↦ ?_)
    have hmp : m.left p ∈ K := by
      change EZ.hom.left (m.left p) ∈ (Set.range q.left)ᶜ
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left]
      simp only [m, Category.assoc, Iso.inv_hom_id, Category.comp_id, Over.comp_left,
        Scheme.Hom.comp_apply]
      exact hmap hp
    have h := hs' _ hmp
    rw [affineCoordinates_spec m] at h
    exact h
  · intro h
    have he : specPoint A (toConv h * toConv g).ofConv ≫ f =
        specPoint A h ≫ f ≫ m := by
      rw [specPoint_mul]
      apply (cancel_mono EZ.hom).mp
      apply (cancel_mono i).mp
      letI := a
      have hid : toUnit (𝟙_ (SchemeOver k)) = 𝟙 (𝟙_ (SchemeOver k)) :=
        (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
      have ht (v : 𝟙_ (SchemeOver k) ⟶ Z) :
          (v ≫ t) ≫ i = gU⁻¹ • (v ≫ i) := by
        change (v ≫ lift (toUnit Z ≫ gU⁻¹) (𝟙 Z) ≫ b.smul) ≫ i =
          lift gU⁻¹ (v ≫ i) ≫ a.smul
        rw [Category.assoc, Category.assoc, hbi, comp_lift_assoc, Category.comp_id,
          comp_toUnit_assoc, hid, Category.id_comp, lift_map_assoc, Category.comp_id]
      have hf (v : 𝟙_ (SchemeOver k) ⟶ (specGroup A).X) :
          (v ≫ f) ≫ EZ.hom ≫ i = (v ≫ E.hom)⁻¹ ≫ orbitMap a x := by
        simp only [f, Category.assoc, Iso.inv_hom_id_assoc, hq]
        rw [← Category.assoc v E.hom, ← Category.assoc (v ≫ E.hom), GrpObj.inv_eq_inv,
          GrpObj.comp_inv, Category.comp_id]
      have hm : m ≫ EZ.hom = EZ.hom ≫ t := by simp [m]
      calc
        ((specPoint A h * specPoint A g) ≫ f) ≫ EZ.hom ≫ i =
            ((specPoint A h * specPoint A g) ≫ E.hom)⁻¹ ≫ orbitMap a x := hf _
        _ = gU⁻¹ • ((specPoint A h ≫ E.hom)⁻¹ ≫ orbitMap a x) := by
          change (((specPoint A h * specPoint A g) ≫ e.hom.hom.hom)⁻¹ ≫ orbitMap a x) = _
          rw [MonObj.mul_comp, rightOrbitEquation]
          rfl
        _ = (specPoint A h ≫ f ≫ m) ≫ EZ.hom ≫ i := by
          rw [← hf, ← Category.assoc (specPoint A h ≫ f) EZ.hom i, ← ht]
          simp only [Category.assoc, reassoc_of% hm]
    apply AlgHom.toRingHom_injective
    have he' := congrArg (fun z : (𝟙_ (SchemeOver k)) ⟶ affineScheme B ↦ z.left) he.symm
    suffices hh : CommRingCat.ofHom (h.comp (r.comp d)).toRingHom =
        CommRingCat.ofHom ((toConv h * toConv g).ofConv.comp r).toRingHom by
      exact congrArg CommRingCat.Hom.hom hh
    apply Spec.map_injective
    change (specPoint A h).left ≫ f.left ≫ m.left =
      (specPoint A (toConv h * toConv g).ofConv).left ≫ f.left at he'
    rw [specPoint_left, specPoint_left, affineCoordinates_spec f, affineCoordinates_spec m] at he'
    rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp] at he'
    exact he'

theorem unipotentOrbitsClosed_conditional
    (_ : BorelQuotientFixedPoints.{u}) (_ : NormalTorusCentral.{u}) (_ : QuotientByCentralizer.{u}) :
    UnipotentOrbitsClosed.{u} := by
  intro k _ _ U X a hs hu ha _ ft x
  letI := ha
  letI := ft
  exact orbitClosure_isClosed U X a hs hu x

open private closed_flag_quotient_proper proper_of_conjugate_quotient
  from LinearAlgebraicGroups.Reductive.BorelProper
open private projection_eq_iff from LinearAlgebraicGroups.Flag.QuotientEmbedding
open private orbitProjection_factors from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private restrictGroupAction restrictGroupAction_smul from LinearAlgebraicGroups.Flag.SmoothOrbit
open private fixed_iff_sections from LinearAlgebraicGroups.Solvable.SplitFixedPoint

private theorem borel_quotient_proper [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left) (B : ClosedSubgroup G.val)
    (hB : IsBorel B) (Q : QuotientEmbedding.Presentation B) : IsProper Q.scheme.hom := by
  obtain ⟨N, P, hN, hp⟩ := closed_flag_quotient_proper
    LinearAlgebraicGroups.GeometricBorelConjugacy.closedFlagOrbitExists
    LinearAlgebraicGroups.GeometricBorelConjugacy.closedFlagStabilizerIsBorel G hs hc
  obtain ⟨g, hg⟩ := LinearAlgebraicGroups.GeometricBorelConjugacy.borelsConjugate G hs hc B N hB hN
  exact proper_of_conjugate_quotient g hg Q P hp

private theorem rational_in_orbitClosure [IsAlgClosed k] {G : GroupScheme k} {X : SchemeOver k}
    (a : ModObj G.X X) (x : 𝟙_ (SchemeOver k) ⟶ X) [QuasiCompact (orbitMap a x).left]
    (y : 𝟙_ (SchemeOver k) ⟶ orbitClosure a x) :
    (y ≫ closureInclusion a x).left (IsLocalRing.closedPoint k) ∈ closure (orbitSet a x) := by
  change (orbitMap a x).left.imageι (y.left (IsLocalRing.closedPoint k)) ∈ _
  rw [show closure (orbitSet a x) = Set.range (orbitMap a x).left.imageι by
    change closure (Set.range (orbitMap a x).left) =
      Set.range (orbitMap a x).left.ker.subschemeι
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]]
  exact ⟨_, rfl⟩

private theorem fixed_point_in_orbit_closure [IsAlgClosed k] (U : AffineAlgebraicGroup k)
    (hs : Smooth U.val.X.hom) (hc : ConnectedSpace U.val.X.left) (hsol : IsSolvable U.val)
    {X : SchemeOver k} [IsProper X.hom] (a : ModObj U.val.X X)
    (x : 𝟙_ (SchemeOver k) ⟶ X) :
    ∃ y : 𝟙_ (SchemeOver k) ⟶ X,
      y.left (IsLocalRing.closedPoint k) ∈ closure (orbitSet a x) ∧ IsFixedBy a.smul y := by
  letI := U.property.1
  letI := U.property.2.1
  letI := hs
  haveI : QuasiCompact (orbitMap a x).left := by
    haveI : IsLocallyNoetherian U.val.X.left :=
      LocallyOfFiniteType.isLocallyNoetherian U.val.X.hom
    haveI : IsNoetherian U.val.X.left := ⟨⟩
    infer_instance
  let Z := orbitClosure a x
  let i := closureInclusion a x
  letI : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion (orbitMap a x).left.imageι)
  haveI : IsProper Z.hom := by rw [← Over.w i]; infer_instance
  have hne : Nonempty Z.left :=
    ⟨(toClosure a x).left (η[U.val.X].left (IsLocalRing.closedPoint k))⟩
  obtain ⟨b, _, hb⟩ := orbitClosure_action a x
  obtain ⟨F, f, _, hf, ⟨z⟩⟩ := BorelFixedPoint.overAlgClosed U Z b hs hc hsol inferInstance hne
  let y := z ≫ f
  refine ⟨y ≫ i, rational_in_orbitClosure a x y, ?_⟩
  letI := a
  rw [fixed_iff_sections (y ≫ i)]
  intro S p g
  letI := b
  change g • (p ≫ y ≫ i) = p ≫ y ≫ i
  have he := ((fixed_iff_sections y).mp ((hf _ y).mpr ⟨z, rfl⟩)) p g
  change lift g (p ≫ y ≫ i) ≫ a.smul = _
  have hm : lift g (p ≫ y) ≫ (𝟙 U.val.X ⊗ₘ i) = lift g (p ≫ y ≫ i) := by
    rw [lift_map, Category.comp_id, Category.assoc]
  rw [← hm, Category.assoc, ← hb, ← Category.assoc, ← Category.assoc p y i]
  exact congrArg (· ≫ i) he

open Specs.GeometricRadicals (IsSplitTorus)
open Specs.CharacterDescent (Character Cocharacter StandardLattice)
open Specs.DiagonalizableGroups (IntegerCharacters integerGenerator groupAlgebra groupAlgebraMap)
open private isTorus_iff_coordinates from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private split_of_torus from LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private splitGroupHomEquiv from LinearAlgebraicGroups.Multiplicative.CharacterDescent

private theorem torus_has_split_coordinates [IsAlgClosed k] {G : AffineAlgebraicGroup k}
    (T : ClosedSubgroup G.val) (hT : GeometricRadicals.IsTorus T.group) :
    IsSplitTorus T.group :=
  split_of_torus ((isTorus_iff_coordinates (closedSubgroupAlgebraicGroup T)).mp hT)

private theorem separates_finite_lattice_weights {idx : Type u} [Finite idx] {r : ℕ}
    (m : idx → StandardLattice.{u} r) :
    ∃ f : StandardLattice.{u} r →* IntegerCharacters.{u},
      ∀ i j, f (m i) = f (m j) → m i = m j := by
  classical
  let p (v : StandardLattice.{u} r) : Polynomial ℤ :=
    ∑ l : Fin r, Polynomial.monomial l.val (v l).down.toAdd
  have hcoeff (v : StandardLattice.{u} r) (l : Fin r) :
      (p v).coeff l.val = (v l).down.toAdd := by
    dsimp only [p]
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single l]
    · exact Polynomial.coeff_monomial_same _ _
    · intro b _ hb
      exact Polynomial.coeff_monomial_of_ne _ (fun h ↦ hb (Fin.ext h.symm))
    · simp
  have hinj : Function.Injective p := by
    intro v w h
    funext l
    apply ULift.ext
    apply Multiplicative.toAdd.injective
    rw [← hcoeff, ← hcoeff, h]
  let E (ij : idx × idx) : Set ℤ :=
    {z | m ij.1 ≠ m ij.2 ∧ (p (m ij.1) - p (m ij.2)).IsRoot z}
  have hE (ij : idx × idx) : (E ij).Finite := by
    by_cases hh : m ij.1 = m ij.2
    · simp [E, hh]
    · exact (Polynomial.finite_setOfPred_isRoot (sub_ne_zero.mpr (fun h ↦ hh (hinj h)))).subset
        (fun _ hz ↦ hz.2)
  obtain ⟨z, hz⟩ := (Set.finite_iUnion hE).exists_notMem
  let f : StandardLattice.{u} r →* IntegerCharacters.{u} :=
    { toFun := fun v ↦ ⟨Multiplicative.ofAdd ((p v).eval z)⟩
      map_one' := by
        apply ULift.ext
        apply Multiplicative.toAdd.injective
        change (p 1).eval z = 0
        simp [p]
      map_mul' v w := by
        apply ULift.ext
        apply Multiplicative.toAdd.injective
        change (p (v * w)).eval z = (p v).eval z + (p w).eval z
        simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial, Pi.mul_apply]
        change (∑ l : Fin r, ((v l).down.toAdd + (w l).down.toAdd) * z ^ l.val) = _
        simp only [add_mul, Finset.sum_add_distrib] }
  refine ⟨f, fun i j h ↦ ?_⟩
  by_contra hc
  apply hz
  refine Set.mem_iUnion.mpr ⟨(i, j), hc, ?_⟩
  have he : (p (m i)).eval z = (p (m j)).eval z :=
    congrArg (fun a : IntegerCharacters.{u} ↦ a.down.toAdd) h
  change (p (m i) - p (m j)).eval z = 0
  rw [Polynomial.eval_sub, sub_eq_zero, he]

private theorem separating_cocharacter {T : GroupScheme k}
    (hT : IsSplitTorus T) {idx : Type u} [Finite idx] (χ : idx → Character T) :
    ∃ t : Cocharacter T, ∀ i j, t ≫ χ i = t ≫ χ j → χ i = χ j := by
  obtain ⟨r, ⟨e₁⟩⟩ := hT
  obtain ⟨e₂⟩ := CharacterDescent.standardSplitTorus (k := k) r
  let E := e₂ ≪≫ e₁.symm
  obtain ⟨p, q, _, _, hcomp⟩ := CharacterDescent.splitCompositionPairing (k := k) r
  let m (i : idx) := p.symm (E.hom ≫ χ i)
  obtain ⟨f, hf⟩ := separates_finite_lattice_weights m
  refine ⟨q f ≫ E.hom, fun i j h ↦ (cancel_epi E.hom).mp ?_⟩
  have he : q f ≫ p (m i) = q f ≫ p (m j) := by
    simpa only [m, MulEquiv.apply_symm_apply, Category.assoc] using h
  change Specs.CharacterDescent.compositionPairing _ (p (m i)) (q f) =
    Specs.CharacterDescent.compositionPairing _ (p (m j)) (q f) at he
  rw [hcomp, hcomp] at he
  have hh := (splitGroupHomEquiv (k := k) IntegerCharacters IntegerCharacters).injective he
  have hz : f (m i) = f (m j) := by
    have he' := DFunLike.congr_fun hh integerGenerator
    change f (m i) ^ (1 : ℤ) = f (m j) ^ (1 : ℤ) at he'
    simpa only [zpow_one] using he'
  have h' := congrArg p (hf i j hz)
  simpa only [m, MulEquiv.apply_symm_apply] using h'

private theorem hom_ext_rational [IsAlgClosed k] {X Y : SchemeOver k}
    [IsReduced X.left] [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom]
    {f g : X ⟶ Y} (h : ∀ p : 𝟙_ (SchemeOver k) ⟶ X, p ≫ f = p ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  haveI : LocallyOfFiniteType (f.left ≫ Y.hom) := Over.w f ▸ inferInstanceAs (LocallyOfFiniteType X.hom)
  refine ext_of_apply_eq Y.hom Set.univ isOpen_univ.isLocallyClosed dense_univ
    (fun x _ hx ↦ ?_) ((Over.w f).trans (Over.w g).symm)
  let p := sectionOfClosedPoint X x hx
  have hp := congrArg (fun a : 𝟙_ (SchemeOver k) ⟶ Y ↦ a.left (IsLocalRing.closedPoint k)) (h p)
  change f.left (p.left (IsLocalRing.closedPoint k)) = g.left (p.left (IsLocalRing.closedPoint k)) at hp
  rwa [sectionOfClosedPoint_apply] at hp

open private centralizes_iff comp_conjugateFamily from LinearAlgebraicGroups.Affine.Stabilizers
open private isPullback_tensor_structure from LinearAlgebraicGroups.Flag.SmoothOrbit

private theorem centralizes_of_commutes_rational [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) {T : GroupScheme k} (i : T ⟶ G.val)
    (hs : Smooth T.X.hom) (g : 𝟙_ (SchemeOver k) ⟶ G.val.X)
    (h : ∀ t : 𝟙_ (SchemeOver k) ⟶ T.X, Commute g (t ≫ i.hom.hom)) : Centralizes i g := by
  letI := hs
  letI := G.property.1
  letI := G.property.2.1
  haveI : IsAffineHom G.val.X.hom := isAffineHom_of_isAffine G.val.X.hom
  let X := T.X ⊗ 𝟙_ (SchemeOver k)
  haveI : Smooth (𝟙_ (SchemeOver k)).hom :=
    inferInstanceAs (Smooth (𝟙 (Spec (CommRingCat.of k))))
  haveI : Smooth X.hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  haveI : IsReduced X.left := isReduced_of_smooth_over_field X.hom
  apply hom_ext_rational
  intro p
  have hp : p ≫ snd T.X (𝟙_ (SchemeOver k)) = 𝟙 _ :=
    (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
  rw [comp_conjugateFamily, ← Category.assoc p (snd _ _) g, hp, Category.id_comp]
  exact mul_inv_eq_iff_eq_mul.mpr (h (p ≫ fst T.X (𝟙_ (SchemeOver k)))).eq

private theorem cocharacter_detects_centralizer [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group)
    (hTs : Smooth T.group.X.hom) {weights : Set (Character T.group)}
    (hw : FaithfulWeights T.inclusion weights) :
    ∃ t : Cocharacter T.group,
      ∀ g : 𝟙_ (SchemeOver k) ⟶ G.val.X,
        Centralizes (t ≫ T.inclusion) g → Centralizes T.inclusion g := by
  classical
  obtain ⟨n, M, e, eₘ, ρ, χ, hρ, _, _, hdiag⟩ := hw
  obtain ⟨t, ht⟩ := separating_cocharacter hT χ
  let R := CommAlgCat.of k k
  let A := (testSpec k).obj (op R)
  let E : A ≅ 𝟙_ (SchemeOver k) :=
    (affineBaseTerminal k).uniqueUpToIso (isTerminalTensorUnit (C := SchemeOver k))
  let mat : (A ⟶ G.val.X) →* Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R :=
    (e.hom.app R).hom.comp (IsMonHom.monoidHom ρ.hom.hom A)
  let D := specGroup (groupAlgebra k IntegerCharacters)
  let wt (s : A ⟶ T.group.X) (j : ULift.{u} (Fin n)) : k :=
    Units.val (show Rˣ from eₘ.hom.app R (s ≫ (χ j).hom.hom))
  have hd (s : A ⟶ T.group.X) :
      (mat (s ≫ T.inclusion.hom.hom)).val = Matrix.diagonal (wt s) := by
    change (e.hom.app R ((s ≫ T.inclusion.hom.hom) ≫ ρ.hom.hom) :
      Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R).val = _
    rw [Category.assoc]
    exact hdiag R s
  letI := hρ
  letI : Mono ρ.hom.hom := Over.mono_of_mono_left _
  have hinj : Function.Injective mat := fun _ _ h ↦
    (cancel_mono ρ.hom.hom).mp ((ConcreteCategory.bijective_of_isIso (e.hom.app R)).1 h)
  have hcharEval {s s' : D ⟶ D}
      (h : ∀ p : A ⟶ D.X, p ≫ s.hom.hom = p ≫ s'.hom.hom) : s = s' := by
    apply Grp.hom_ext
    letI : UniqueProds IntegerCharacters.{u} :=
      MulEquiv.ulift.uniqueProds_iff.mpr (inferInstance : UniqueProds (Multiplicative ℤ))
    let eI : Multiplicative ℤ ≃* IntegerCharacters.{u} := MulEquiv.ulift.symm
    letI : Group.FG IntegerCharacters.{u} := Group.fg_of_surjective (f := eI.toMonoidHom) eI.surjective
    haveI : IsReduced D.X.left := (affine_isReduced_iff _).mpr (inferInstanceAs
      (IsReduced (MonoidAlgebra k IntegerCharacters)))
    haveI : LocallyOfFiniteType D.X.hom := (hopfSpec_locallyOfFiniteType_iff k _).mpr inferInstance
    haveI : IsAffine D.X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of
      (MonoidAlgebra k IntegerCharacters))))
    haveI : IsAffineHom D.X.hom := isAffineHom_of_isAffine D.X.hom
    apply hom_ext_rational
    intro p
    apply (cancel_epi E.hom).mp
    simpa only [Category.assoc] using h (E.hom ≫ p)
  refine ⟨t, fun g hg ↦ centralizes_of_commutes_rational G T.inclusion hTs g (fun s ↦ ?_)⟩
  let x := mat (E.hom ≫ g)
  have hzero (i j : ULift.{u} (Fin n)) (hij : χ i ≠ χ j) : x.val i j = 0 := by
    by_contra hne
    apply hij
    apply ht
    apply hcharEval
    intro p
    have hcomm := ((centralizes_iff (t ≫ T.inclusion) g).mp hg A E.hom p).map mat
    have he := congrArg (fun m : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) R ↦ m.val i j) hcomm.eq
    change (x.val * (mat ((p ≫ t.hom.hom) ≫ T.inclusion.hom.hom)).val) i j =
      ((mat ((p ≫ t.hom.hom) ≫ T.inclusion.hom.hom)).val * x.val) i j at he
    rw [hd, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm (wt _ i)] at he
    have hval : wt (p ≫ t.hom.hom) i = wt (p ≫ t.hom.hom) j := (mul_left_cancel₀ hne he).symm
    have hunit : eₘ.hom.app R ((p ≫ t.hom.hom) ≫ (χ i).hom.hom) =
        eₘ.hom.app R ((p ≫ t.hom.hom) ≫ (χ j).hom.hom) := Units.ext hval
    exact (ConcreteCategory.bijective_of_isIso (eₘ.hom.app R)).1 hunit
  change g * (s ≫ T.inclusion.hom.hom) = (s ≫ T.inclusion.hom.hom) * g
  apply (cancel_epi E.hom).mp
  rw [MonObj.comp_mul, MonObj.comp_mul, ← Category.assoc E.hom s]
  apply hinj
  rw [map_mul, map_mul]
  apply Units.ext
  ext i j
  change (x.val * (mat ((E.hom ≫ s) ≫ T.inclusion.hom.hom)).val) i j =
    ((mat ((E.hom ≫ s) ≫ T.inclusion.hom.hom)).val * x.val) i j
  rw [hd, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hh : χ i = χ j
  · have he : wt (E.hom ≫ s) i = wt (E.hom ≫ s) j :=
      congrArg (fun a : Character T.group ↦
        Units.val (show Rˣ from eₘ.hom.app R ((E.hom ≫ s) ≫ a.hom.hom))) hh
    rw [he, mul_comm]
  · rw [hzero i j hh, zero_mul, mul_zero]

open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition oppositeCocharacter
  existsLimitDecomposition limitSubgroupsSmooth geometricallyConnectedLimitSubgroups
  contractingSubgroupUnipotent bigCell bigCellMap multiplyFactors)
open private centralizes_iff_affine from LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer
open private unitEquiv unitPointHom unitPointHom_apply opposite_point
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient

private theorem centralizes_opposite {G : GroupScheme k} (t : Cocharacter G)
    {Y : SchemeOver k} (g : Y ⟶ G.X) :
    Centralizes (oppositeCocharacter t) g ↔ Centralizes t g := by
  rw [centralizes_iff_affine, centralizes_iff_affine]
  constructor
  · intro h R y p
    obtain ⟨z, rfl⟩ := (unitEquiv R).symm.surjective p
    have hp := h R y (CocharacterDynamics.unitPoint R z⁻¹)
    change Commute (y ≫ g) (CocharacterDynamics.cocharacterPoint (oppositeCocharacter t) R z⁻¹) at hp
    rw [opposite_point, inv_inv] at hp
    change Commute (y ≫ g) (CocharacterDynamics.cocharacterPoint t R z)
    exact hp
  · intro h R y p
    obtain ⟨z, rfl⟩ := (unitEquiv R).symm.surjective p
    have hp := h R y (CocharacterDynamics.unitPoint R z⁻¹)
    change Commute (y ≫ g) (((groupPointsFunctor k).map (oppositeCocharacter t)).app R (unitPointHom R z))
    rw [unitPointHom_apply]
    change Commute (y ≫ g) (CocharacterDynamics.cocharacterPoint (oppositeCocharacter t) R z)
    rwa [opposite_point]

private theorem split_torus_sections_commute {T : GroupScheme k} (hT : IsSplitTorus T)
    {X : SchemeOver k} (a b : X ⟶ T.X) : Commute a b := by
  obtain ⟨r, ⟨e₁⟩⟩ := hT
  obtain ⟨e₂⟩ := CharacterDescent.standardSplitTorus (k := k) r
  let e := e₁ ≪≫ e₂.symm
  haveI : IsIso e.hom.hom.hom := (Grp.forget (SchemeOver k)).map_isIso e.hom
  apply (cancel_mono e.hom.hom.hom).mp
  rw [MonObj.mul_comp, MonObj.mul_comp]
  exact mul_comm _ _

private theorem normalizes_of_centralizes {G T : GroupScheme k} {Y : SchemeOver k}
    {i : T ⟶ G} {g : Y ⟶ G.X} (h : Centralizes i g) : Normalizes i g :=
  ⟨Iso.refl _, Category.id_comp _, (Category.id_comp _).trans h.symm⟩

private theorem centralizing_point_mem_borel [IsAlgClosed k] {G : GroupScheme k}
    (T B N : ClosedSubgroup G) (Q : QuotientEmbedding.Presentation B)
    (hN : RepresentsSubgroup N (fun _ g ↦ Normalizes T.inclusion g))
    (hQ : ∀ n₁ n₂ : 𝟙_ (SchemeOver k) ⟶ N.group.X,
      (n₁ ≫ N.inclusion.hom.hom ≫ Q.projection = n₂ ≫ N.inclusion.hom.hom ≫ Q.projection) ↔
        Centralizes T.inclusion ((n₂⁻¹ * n₁) ≫ N.inclusion.hom.hom))
    (g : 𝟙_ (SchemeOver k) ⟶ G.X) (hg : Centralizes T.inclusion g) :
    g ∈ SubgroupSections B (𝟙_ (SchemeOver k)) := by
  obtain ⟨n, hn⟩ := (hN _ g).mp (normalizes_of_centralizes hg)
  have he := (hQ n (1 : 𝟙_ (SchemeOver k) ⟶ N.group.X)).mpr (by
    simpa only [inv_one, one_mul, hn] using hg)
  rw [← Category.assoc n, hn, ← Category.assoc (1 : 𝟙_ (SchemeOver k) ⟶ N.group.X),
    MonObj.one_comp] at he
  simpa only [inv_one, one_mul] using (projection_eq_iff Q 1 g).mp he.symm

private theorem limit_parabolic_solvable [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    [Smooth G.val.X.hom] [ConnectedSpace G.val.X.left] {t : Cocharacter G.val}
    (D : LimitDecomposition t) {B : ClosedSubgroup G.val} (hB : IsBorel B)
    (hC : ∀ g : 𝟙_ (SchemeOver k) ⟶ G.val.X, Centralizes t g →
      g ∈ SubgroupSections B (𝟙_ (SchemeOver k))) :
    IsSmoothConnectedSolvable D.parabolic := by
  obtain ⟨hsP, hsU, hsC⟩ := limitSubgroupsSmooth G t D
  obtain ⟨hcP, hcU, _⟩ := geometricallyConnectedLimitSubgroups G t D
  have hconnP : ConnectedSpace D.parabolic.group.X.left := by
    letI := hcP
    exact GeometricallyConnected.connectedSpace_of_subsingleton D.parabolic.group.X.hom
  have hconnU : ConnectedSpace D.contracting.group.X.left := by
    letI := hcU
    exact GeometricallyConnected.connectedSpace_of_subsingleton D.contracting.group.X.hom
  let C := D.centralizer
  have hCB : IsSubgroupOf C B := by
    haveI := hsC
    haveI : IsReduced C.group.X.left := isReduced_of_smooth_over_field C.group.X.hom
    apply subgroup_of_sections
    change ∃ f : C.group.X ⟶ B.group.X, f ≫ B.inclusion.hom.hom = C.inclusion.hom.hom
    apply factors_through_closed_of_rational_points B.inclusion.hom.hom B.isClosedImmersion
    intro z
    exact hC _ ((D.centralizer_points _ _).mpr ⟨z, rfl⟩)
  obtain ⟨l, hl⟩ := hCB
  letI : IsClosedImmersion l.hom.hom.left := factor_closed hl
  letI : Mono l.hom.hom := Over.mono_of_mono_left _
  letI : Group.IsSolvable (𝟙_ (SchemeOver k) ⟶ B.group.X) :=
    (solvable_iff_sections (closedSubgroupAlgebraicGroup B) hB.1.1 hB.1.2.1).mp hB.1.2.2
  letI : Group.IsSolvable (𝟙_ (SchemeOver k) ⟶ C.group.X) :=
    Group.isSolvable_of_isSolvable_injective (f := rationalMap l)
      (fun _ _ h ↦ (cancel_mono l.hom.hom).mp h)
  let U := closedSubgroupAlgebraicGroup D.contracting
  have hu := contractingSubgroupUnipotent G t D
  letI : Group.IsSolvable (rationalSections D.contracting.group) :=
    (solvable_iff_sections U hsU hconnU).mp (unipotent_solvable U hsU hconnU hu)
  let j := rationalMap D.contractingToParabolic
  let p := rationalMap D.limit
  have hker : p.ker ≤ j.range := by
    intro x hx
    have hci : IsClosedImmersion D.contractingToParabolic.hom.hom.left :=
      factor_closed D.contracting_in_G
    let N : ClosedSubgroup D.parabolic.group := ⟨_, D.contractingToParabolic, hci⟩
    exact (schemeKernel_sections (N := N) D.isKernel x).mpr hx
  exact ⟨hsP, hconnP, (solvable_iff_sections (closedSubgroupAlgebraicGroup D.parabolic) hsP hconnP).mpr
    (Group.isSolvable_of_ker_le_range j p hker)⟩

private theorem torus_in_limit_parabolic {G : GroupScheme k} (T : ClosedSubgroup G)
    (hT : IsSplitTorus T.group) {t : Cocharacter G}
    (D : LimitDecomposition t) (ht : ∃ c : Cocharacter T.group, c ≫ T.inclusion = t) :
    IsSubgroupOf T D.parabolic := by
  obtain ⟨c, rfl⟩ := ht
  have h : Centralizes (c ≫ T.inclusion) T.inclusion.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro X a b
    have hm := (split_torus_sections_commute hT a (b ≫ c.hom.hom)).map
      (IsMonHom.monoidHom T.inclusion.hom.hom X)
    exact hm
  obtain ⟨v, hv⟩ := (D.centralizer_points _ _).mp h
  exact subgroupOf_trans (factor_group_through_subgroup D.centralizer T.inclusion v hv)
    ⟨D.sectionMap, D.section_in_G⟩

/-- The two cocharacter limit subgroups lie in Borels whose product contains the open cell. -/
private theorem borels_with_dense_product [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    [Smooth G.val.X.hom] [ConnectedSpace G.val.X.left]
    (T : ClosedSubgroup G.val) (hT : IsMaximalTorus T) (hTs : IsSplitTorus T.group)
    (fixed : BorelQuotientFixedPoints.{u}) (N : ClosedSubgroup G.val)
    (hN : RepresentsSubgroup N (fun _ g ↦ Normalizes T.inclusion g))
    {weights : Set (Character T.group)} (hw : FaithfulWeights T.inclusion weights) :
    ∃ (L B : ClosedSubgroup G.val), IsBorel L ∧ IsBorel B ∧ IsSubgroupOf T L ∧ IsSubgroupOf T B ∧
      DenseRange (multiplyFactors L.inclusion B.inclusion).left := by
  have hsm : Smooth G.val.X.hom := inferInstance
  have hconn : ConnectedSpace G.val.X.left := inferInstance
  obtain ⟨B₀, hB₀, hTB₀⟩ := LinearAlgebraicGroups.GeometricBorelConjugacy.torusContainedInBorel
    G hsm hconn T hT.1
  obtain ⟨Q₀⟩ := HomogeneousQuotient.homogeneousQuotient k G B₀ |>.1
  obtain ⟨_, _, _, _, hEq, _⟩ := fixed G hsm hconn T B₀ hT hB₀ hTB₀ N hN Q₀
  have hcent (g : 𝟙_ (SchemeOver k) ⟶ G.val.X) (hg : Centralizes T.inclusion g) :
      g ∈ SubgroupSections B₀ (𝟙_ (SchemeOver k)) :=
    centralizing_point_mem_borel T B₀ N Q₀ hN hEq g hg
  have htSmooth := (torus_smooth_connected_solvable (closedSubgroupAlgebraicGroup T) hT.1).1
  obtain ⟨t, ht⟩ := cocharacter_detects_centralizer G T hTs htSmooth hw
  let c := t ≫ T.inclusion
  obtain ⟨D⟩ := existsLimitDecomposition G c
  obtain ⟨Dn⟩ := existsLimitDecomposition G (oppositeCocharacter c)
  have hP := limit_parabolic_solvable G D hB₀ (fun g hg ↦ hcent g (ht g hg))
  have hPn := limit_parabolic_solvable G Dn hB₀ (fun g hg ↦ hcent g
    (ht g ((centralizes_opposite c g).mp hg)))
  obtain ⟨B, hB, ⟨j, hj⟩⟩ := exists_borel_above G D.parabolic hP
  obtain ⟨L, hL, ⟨jn, hjn⟩⟩ := exists_borel_above G Dn.parabolic hPn
  have hTB := subgroupOf_trans (torus_in_limit_parabolic T hTs D ⟨t, rfl⟩) ⟨j, hj⟩
  have hTL := subgroupOf_trans (torus_in_limit_parabolic T hTs Dn
    ⟨oppositeCocharacter t, Category.assoc _ _ _⟩) ⟨jn, hjn⟩
  refine ⟨L, B, hL, hB, hTL, hTB, ?_⟩
  let a := (Dn.contractingToParabolic ≫ jn).hom.hom
  let b := multiplyFactors (D.sectionMap ≫ j) (D.contractingToParabolic ≫ j)
  have hmap : (a ⊗ₘ b) ≫ multiplyFactors L.inclusion B.inclusion = bigCellMap D Dn := by
    have e₁ : Dn.contractingToParabolic ≫ jn ≫ L.inclusion = Dn.contracting.inclusion :=
      (congrArg (Dn.contractingToParabolic ≫ ·) hjn).trans Dn.contracting_in_G
    have e₂ : D.sectionMap ≫ j ≫ B.inclusion = D.centralizer.inclusion :=
      (congrArg (D.sectionMap ≫ ·) hj).trans D.section_in_G
    have e₃ : D.contractingToParabolic ≫ j ≫ B.inclusion = D.contracting.inclusion :=
      (congrArg (D.contractingToParabolic ≫ ·) hj).trans D.contracting_in_G
    simp only [bigCellMap, multiplyFactors, MonObj.comp_mul, tensorHom_fst_assoc,
      tensorHom_snd_assoc, a, b, MonObj.mul_comp, Category.assoc]
    rw [show (Dn.contractingToParabolic ≫ jn).hom.hom ≫ L.inclusion.hom.hom =
          Dn.contracting.inclusion.hom.hom from
        congrArg (Grp.forget (SchemeOver k)).map ((Category.assoc _ _ _).trans e₁),
      show (D.sectionMap ≫ j).hom.hom ≫ B.inclusion.hom.hom = D.centralizer.inclusion.hom.hom from
        congrArg (Grp.forget (SchemeOver k)).map ((Category.assoc _ _ _).trans e₂),
      show (D.contractingToParabolic ≫ j).hom.hom ≫ B.inclusion.hom.hom =
          D.contracting.inclusion.hom.hom from
        congrArg (Grp.forget (SchemeOver k)).map ((Category.assoc _ _ _).trans e₃)]
  haveI : IsOpenImmersion (bigCellMap D Dn).left := bigCell G c D Dn
  haveI : IsIntegral G.val.X.left := WordDomainGeometry.smoothConnectedGroupIntegral G hsm hconn
  have hne : (Set.range (bigCellMap D Dn).left).Nonempty :=
    ⟨_, lift η[Dn.contracting.group.X] (lift η[D.centralizer.group.X] η[D.contracting.group.X]) |>.left
      <| IsLocalRing.closedPoint k, rfl⟩
  refine ((bigCellMap D Dn).left.isOpenEmbedding.isOpen_range.dense hne).mono ?_
  rw [← hmap, Over.comp_left]
  change Set.range ((multiplyFactors L.inclusion B.inclusion).left ∘ (a ⊗ₘ b).left) ⊆ _
  exact Set.range_comp_subset_range _ _

open private affine_tensor from LinearAlgebraicGroups.Solvable.FiniteWordClosure

@[instance_reducible] private def twoSidedAction {H G : GroupScheme k} (l r : H ⟶ G) :
    ModObj H.X G.X := by
  let m : H.X ⊗ G.X ⟶ G.X :=
    (fst H.X G.X ≫ l.hom.hom) * snd H.X G.X * (fst H.X G.X ≫ r.hom.hom)⁻¹
  have hm {Y : SchemeOver k} (a : Y ⟶ H.X) (b : Y ⟶ G.X) :
      lift a b ≫ m = (a ≫ l.hom.hom) * b * (a ≫ r.hom.hom)⁻¹ := by
    simp only [m, MonObj.comp_mul, GrpObj.comp_inv, lift_fst_assoc, lift_snd]
  refine ⟨m, ?_, ?_⟩
  · change η[H.X] ▷ G.X ≫ m = (λ_ G.X).hom
    have he : η[H.X] ▷ G.X = lift (fst (𝟙_ (SchemeOver k)) G.X ≫ η[H.X]) (snd _ _) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [whiskerRight_fst, lift_fst]
      · rw [whiskerRight_snd, lift_snd]
    rw [he, hm, Category.assoc, Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
    have h1 : fst (𝟙_ (SchemeOver k)) G.X ≫ η[G.X] = 1 := by
      rw [CategoryTheory.Hom.one_def, toUnit_unique (fst _ _) (toUnit _)]
    simp only [h1, inv_one, one_mul, mul_one, CartesianMonoidalCategory.leftUnitor_hom]
  · change μ[H.X] ▷ G.X ≫ m = (α_ H.X H.X G.X).hom ≫ (H.X ◁ m) ≫ m
    let Y := (H.X ⊗ H.X) ⊗ G.X
    let z := fst (H.X ⊗ H.X) G.X
    let a : Y ⟶ H.X := z ≫ fst H.X H.X
    let b : Y ⟶ H.X := z ≫ snd H.X H.X
    let c : Y ⟶ G.X := snd _ _
    have hl : μ[H.X] ▷ G.X = lift (a * b) c := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [whiskerRight_fst, lift_fst, a, b, CategoryTheory.Hom.mul_def, ← comp_lift,
          lift_fst_snd, Category.comp_id, z]
      · rw [whiskerRight_snd, lift_snd]
    have hr : (α_ H.X H.X G.X).hom ≫ (H.X ◁ m) = lift a (lift b c ≫ m) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, whiskerLeft_fst, associator_hom_fst, lift_fst, a, z]
      · rw [Category.assoc, whiskerLeft_snd, lift_snd, ← Category.assoc]
        congr 1
        apply CartesianMonoidalCategory.hom_ext
        · simp only [Category.assoc, b, z, associator_hom_snd_fst, lift_fst]
        · simp only [Category.assoc, c, associator_hom_snd_snd, lift_snd]
    rw [hl, ← Category.assoc, hr, hm, hm, hm, MonObj.mul_comp, MonObj.mul_comp]
    group

/-- A product of two smooth unipotent subgroups is a two-sided orbit on the affine group. -/
private theorem closed_product_of_unipotent_subgroups [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) (J L : ClosedSubgroup G.val)
    (hsJ : Smooth J.group.X.hom) (hsL : Smooth L.group.X.hom)
    (huJ : IsUnipotent (closedSubgroupAlgebraicGroup J))
    (huL : IsUnipotent (closedSubgroupAlgebraicGroup L)) :
    IsClosed (Set.range (multiplyFactors J.inclusion L.inclusion).left) := by
  let F := Grp.forget (SchemeOver k)
  let W : GroupScheme k := J.group ⨯ L.group
  let p₁ : W ⟶ J.group := prod.fst
  let p₂ : W ⟶ L.group := prod.snd
  let D := (tensorProductIsBinaryProduct J.group.X L.group.X).conePointUniqueUpToIso
    (prodIsProd J.group.X L.group.X)
  let E : W.X ≅ J.group.X ⊗ L.group.X := PreservesLimitPair.iso F _ _ ≪≫ D.symm
  have h₁ : E.hom ≫ fst J.group.X L.group.X = p₁.hom.hom := by
    change (PreservesLimitPair.iso F _ _).hom ≫ D.inv ≫ fst _ _ = p₁.hom.hom
    rw [show D.inv ≫ fst J.group.X L.group.X = prod.fst from
      IsLimit.conePointUniqueUpToIso_inv_comp (tensorProductIsBinaryProduct J.group.X L.group.X)
        (prodIsProd J.group.X L.group.X) ⟨WalkingPair.left⟩,
      PreservesLimitPair.iso_hom]
    exact Limits.prodComparison_fst F J.group L.group
  have h₂ : E.hom ≫ snd J.group.X L.group.X = p₂.hom.hom := by
    change (PreservesLimitPair.iso F _ _).hom ≫ D.inv ≫ snd _ _ = p₂.hom.hom
    rw [show D.inv ≫ snd J.group.X L.group.X = prod.snd from
      IsLimit.conePointUniqueUpToIso_inv_comp (tensorProductIsBinaryProduct J.group.X L.group.X)
        (prodIsProd J.group.X L.group.X) ⟨WalkingPair.right⟩,
      PreservesLimitPair.iso_hom]
    exact Limits.prodComparison_snd F J.group L.group
  letI : IsAffine J.group.X.left := (closedSubgroupAlgebraicGroup J).property.1
  letI : IsAffine L.group.X.left := (closedSubgroupAlgebraicGroup L).property.1
  letI := hsJ
  letI := hsL
  letI : IsAffine (J.group.X ⊗ L.group.X).left := affine_tensor
  letI : IsIso E.hom.left := (Over.forget _).map_isIso E.hom
  letI : IsAffine W.X.left := isAffine_of_isAffineHom E.hom.left
  haveI : Smooth (J.group.X ⊗ L.group.X).hom := by rw [Over.tensorObj_hom]; infer_instance
  have hw : Smooth W.X.hom := by rw [← Over.w E.hom]; infer_instance
  letI := hw
  letI : IsAffineHom W.X.hom := isAffineHom_of_isAffine W.X.hom
  let A : AffineAlgebraicGroup k := ⟨W, inferInstance, inferInstance, inferInstance⟩
  have hsurjJ : Surjective J.group.X.hom :=
    ⟨fun y ↦ ⟨η[J.group.X].left (IsLocalRing.closedPoint k), Subsingleton.elim _ _⟩⟩
  haveI : Surjective (snd J.group.X L.group.X).left := MorphismProperty.of_isPullback
    (isPullback_tensor_structure J.group.X L.group.X) hsurjJ
  haveI : Smooth (snd J.group.X L.group.X).left := MorphismProperty.of_isPullback
    (isPullback_tensor_structure J.group.X L.group.X) hsJ
  have hpflat : Flat p₂.hom.hom.left := by rw [← h₂, Over.comp_left]; infer_instance
  have hpsurj : Surjective p₂.hom.hom.left := by rw [← h₂, Over.comp_left]; infer_instance
  let z : J.group ⟶ L.group := Grp.homMk'' (1 : J.group.X ⟶ L.group.X)
    (by rw [MonObj.comp_one, MonObj.one_eq_one])
    (by
      have he : (1 : J.group.X ⟶ L.group.X) ⊗ₘ (1 : J.group.X ⟶ L.group.X) =
          lift (fst J.group.X J.group.X ≫ (1 : J.group.X ⟶ L.group.X))
            (snd J.group.X J.group.X ≫ (1 : J.group.X ⟶ L.group.X)) := by
        rw [← lift_map, lift_fst_snd, Category.id_comp]
      rw [he, ← CategoryTheory.Hom.mul_def, MonObj.comp_one, MonObj.comp_one, MonObj.comp_one, one_mul])
  let j : J.group ⟶ W := prod.lift (𝟙 _) z
  have hj₁ : j.hom.hom ≫ p₁.hom.hom = 𝟙 J.group.X :=
    congrArg F.map (prod.lift_fst (𝟙 J.group) z)
  have hj₂ : j.hom.hom ≫ p₂.hom.hom = 1 :=
    congrArg F.map (prod.lift_snd (𝟙 J.group) z)
  have hext {Y : SchemeOver k} {f g : Y ⟶ W.X}
      (hfst : f ≫ p₁.hom.hom = g ≫ p₁.hom.hom)
      (hsnd : f ≫ p₂.hom.hom = g ≫ p₂.hom.hom) : f = g := by
    apply (cancel_mono E.hom).mp
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc, h₁] using hfst
    · simpa only [Category.assoc, h₂] using hsnd
  have hk : IsPullback j.hom.hom (toUnit J.group.X) p₂.hom.hom η[L.group.X] := by
    apply IsPullback.mk' (hj₂.trans CategoryTheory.Hom.one_def)
    · intro Y a b hₐ _
      simpa only [Category.assoc, hj₁, Category.comp_id] using
        congrArg (· ≫ p₁.hom.hom) hₐ
    · intro Y a b hab
      refine ⟨a ≫ p₁.hom.hom, hext ?_ ?_, (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _⟩
      · simp only [Category.assoc, hj₁, Category.comp_id]
      · rw [Category.assoc, Category.assoc, hj₂, MonObj.comp_one, hab,
          toUnit_unique b (toUnit Y), CategoryTheory.Hom.one_def, comp_toUnit_assoc]
  have hz : IsClosedImmersion (η[L.group.X]).left :=
    isClosedImmersion_of_comp_eq_id L.group.X.hom _ (Over.w η[L.group.X])
  let N : ClosedSubgroup A.val :=
    ⟨_, j, MorphismProperty.of_isPullback (hk.map (Over.forget _)).flip hz⟩
  have hu : IsUnipotent A :=
    Unipotent.extensionsUnipotent A (closedSubgroupAlgebraicGroup L) p₂ N hk hpflat hpsurj huJ huL
  let a := twoSidedAction (p₁ ≫ J.inclusion) (p₂ ≫ L.inclusion)
  letI := G.property.1
  letI := G.property.2.1
  have hclosed := orbitClosure_isClosed A G.val.X a hw hu η[G.val.X]
  have hOrbit : orbitMap a η[G.val.X] =
      (E.hom ≫ (𝟙 J.group.X ⊗ₘ ι[L.group.X])) ≫ multiplyFactors J.inclusion L.inclusion := by
    change lift (𝟙 W.X) (toUnit W.X ≫ η[G.val.X]) ≫
        ((fst W.X G.val.X ≫ (p₁ ≫ J.inclusion).hom.hom) * snd W.X G.val.X *
          (fst W.X G.val.X ≫ (p₂ ≫ L.inclusion).hom.hom)⁻¹) = _
    simp only [MonObj.comp_mul, GrpObj.comp_inv, lift_fst_assoc, Category.id_comp, lift_snd,
      ← CategoryTheory.Hom.one_def, mul_one, multiplyFactors, Category.assoc, tensorHom_fst_assoc,
      tensorHom_snd_assoc, reassoc_of% h₁, reassoc_of% h₂, GrpObj.inv_eq_inv]
    have hh : p₂.hom.hom ≫ (𝟙 L.group.X)⁻¹ ≫ L.inclusion.hom.hom =
        (p₂.hom.hom ≫ L.inclusion.hom.hom)⁻¹ := by
      rw [← Category.assoc, GrpObj.comp_inv, Category.comp_id, GrpObj.inv_comp]
    rw [hh]
    rfl
  rw [orbitSet, hOrbit, Over.comp_left] at hclosed
  change IsClosed (Set.range ((multiplyFactors J.inclusion L.inclusion).left ∘
    (E.hom ≫ (𝟙 J.group.X ⊗ₘ ι[L.group.X])).left)) at hclosed
  haveI : IsIso (E.hom ≫ (𝟙 J.group.X ⊗ₘ ι[L.group.X])).left :=
    (Over.forget (Spec (CommRingCat.of k))).map_isIso (E.hom ≫ (𝟙 J.group.X ⊗ₘ ι[L.group.X]))
  rw [(E.hom ≫ (𝟙 J.group.X ⊗ₘ ι[L.group.X])).left.surjective.range_comp] at hclosed
  exact hclosed

private theorem orbitMap_restrict {H G : GroupScheme k} {X : SchemeOver k}
    (f : H ⟶ G) (a : ModObj G.X X) (x : 𝟙_ (SchemeOver k) ⟶ X) :
    orbitMap (restrictGroupAction f a) x = f.hom.hom ≫ orbitMap a x := by
  simp only [orbitMap, restrictGroupAction_smul, lift_map_assoc, Category.id_comp, Category.comp_id,
    comp_lift_assoc, comp_toUnit_assoc]

private theorem orbitPresentation_range {G : GroupScheme k} {X : SchemeOver k}
    {a : ModObj G.X X} {x : 𝟙_ (SchemeOver k) ⟶ X} (P : Specs.SmoothOrbit.Presentation a x) :
    Set.range (P.openInClosure ≫ closureInclusion a x).left = orbitSet a x := by
  let i := P.openInClosure ≫ closureInclusion a x
  letI := P.surjective
  rw [orbitSet, ← orbitProjection_factors P, Over.comp_left]
  exact (P.projection.left.surjective.range_comp i.left).symm

private theorem orbit_locallyClosed (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) {X : SchemeOver k} [IsSeparated X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (a : ModObj G.val.X X) (x : 𝟙_ (SchemeOver k) ⟶ X) :
    IsLocallyClosed (orbitSet a x) := by
  obtain ⟨P⟩ := SmoothOrbit.schemeOrbit k G X a x hs inferInstance inferInstance inferInstance
  letI : IsOpenImmersion P.openInClosure.left := P.isOpen
  rw [← orbitPresentation_range P]
  change IsLocallyClosed (Set.range (P.openInClosure.left ≫ (orbitMap a x).left.imageι))
  exact (P.openInClosure.left ≫ (orbitMap a x).left.imageι).isLocallyClosed_range

private theorem orbit_closed_inside_unipotent_orbit [IsAlgClosed k]
    (U : AffineAlgebraicGroup k) (hs : Smooth U.val.X.hom) (hu : IsUnipotent U)
    (H : ClosedSubgroup U.val) (hHs : Smooth H.group.X.hom)
    {X : SchemeOver k} [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (a : ModObj U.val.X X) (x : 𝟙_ (SchemeOver k) ⟶ X)
    {y : X.left} (hy : y ∈ orbitSet a x)
    (hyC : y ∈ closure (orbitSet (restrictGroupAction H.inclusion a) x)) :
    y ∈ orbitSet (restrictGroupAction H.inclusion a) x := by
  let b := restrictGroupAction H.inclusion a
  let q := orbitMap a x
  let C := orbitSet b x
  letI := a
  obtain ⟨P⟩ := SmoothOrbit.schemeOrbit k U X a x hs inferInstance inferInstance inferInstance
  let i := P.openInClosure ≫ closureInclusion a x
  have hi : P.projection ≫ i = q := orbitProjection_factors P
  have hC : C ⊆ Set.range i.left := by
    rw [orbitPresentation_range P]
    change Set.range (orbitMap b x).left ⊆ Set.range q.left
    rw [orbitMap_restrict, Over.comp_left]
    change Set.range (⇑q.left ∘ ⇑H.inclusion.hom.hom.left) ⊆ _
    exact Set.range_comp_subset_range _ _
  let L := P.stabilizer
  obtain ⟨D, hDs, _, hD⟩ :=
    EquivariantUnipotentSeries.exists_smooth_reduction (closedSubgroupAlgebraicGroup L)
  let S := subgroupOfSubgroup L D
  have huH := Unipotent.closedSubgroupsUnipotent U H hu
  have huS := Unipotent.closedSubgroupsUnipotent U S hu
  let m := multiplyFactors H.inclusion S.inclusion
  have hm : IsClosed (Set.range m.left) :=
    closed_product_of_unipotent_subgroups U H S hHs hDs huH huS
  have hpre : q.left ⁻¹' C = Set.range m.left := by
    refine Set.Subset.antisymm ?_ ?_
    · intro u hu₁
      by_contra hu₂
      letI := U.property.2.1
      haveI : JacobsonSpace U.val.X.left := LocallyOfFiniteType.jacobsonSpace U.val.X.hom
      have hloc : IsLocallyClosed ((q.left ⁻¹' C) ∩ (Set.range m.left)ᶜ) :=
        ((orbit_locallyClosed (closedSubgroupAlgebraicGroup H) hHs b x).preimage q.left.continuous).inter
          hm.isOpen_compl.isLocallyClosed
      have hn : (q.left ⁻¹' C ∩ (Set.range m.left)ᶜ).Nonempty := ⟨u, hu₁, hu₂⟩
      obtain ⟨w, hw, hwc⟩ := nonempty_inter_closedPoints hn hloc
      let v := sectionOfClosedPoint U.val.X w hwc
      let z := v ≫ q
      have hz : z.left (IsLocalRing.closedPoint k) ∈ C := by
        change q.left (v.left (IsLocalRing.closedPoint k)) ∈ C
        rw [sectionOfClosedPoint_apply]
        exact hw.1
      obtain ⟨h, he⟩ := (SmoothOrbit.geometricOrbitLifts k (closedSubgroupAlgebraicGroup H) X b x z).mp hz
      let r := h ≫ H.inclusion.hom.hom
      have her : r • x = v • x := by
        have eunit : toUnit (𝟙_ (SchemeOver k)) = 𝟙 (𝟙_ (SchemeOver k)) :=
          (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
        rw [orbitMap_restrict, ← Category.assoc, orbitMap_comp, eunit, Category.id_comp] at he
        rw [he]
        change v ≫ orbitMap a x = _
        rw [orbitMap_comp, eunit, Category.id_comp]
      have hfix : Stabilizes a.smul x (r⁻¹ * v) := by
        have eunit : toUnit (𝟙_ (SchemeOver k)) = 𝟙 (𝟙_ (SchemeOver k)) :=
          (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
        change (r⁻¹ * v) • (toUnit (𝟙_ (SchemeOver k)) ≫ x) = _
        rw [eunit, Category.id_comp, mul_smul, ← her, inv_smul_smul]
      obtain ⟨l, hl⟩ := (P.representsStabilizer _ _).mp hfix
      letI : IsReduced (𝟙_ (SchemeOver k)).left :=
        inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
      obtain ⟨d, hd⟩ := hD (𝟙_ (SchemeOver k)) l
      have hl' : d ≫ S.inclusion.hom.hom = r⁻¹ * v := by
        change d ≫ D.inclusion.hom.hom ≫ L.inclusion.hom.hom = _
        rw [← Category.assoc, hd]
        exact hl
      have hprod : lift h d ≫ m = v := by
        have hleft : lift h d ≫ fst H.group.X S.group.X ≫ H.inclusion.hom.hom =
            h ≫ H.inclusion.hom.hom := lift_fst_assoc _ _ _
        have hright : lift h d ≫ snd H.group.X S.group.X ≫ S.inclusion.hom.hom =
            d ≫ S.inclusion.hom.hom := lift_snd_assoc _ _ _
        change lift h d ≫ ((fst H.group.X S.group.X ≫ H.inclusion.hom.hom) *
          (snd H.group.X S.group.X ≫ S.inclusion.hom.hom)) = _
        rw [MonObj.comp_mul, hleft, hright, hl', ← mul_assoc, mul_inv_cancel, one_mul]
      apply hw.2
      refine ⟨(lift h d).left (IsLocalRing.closedPoint k), ?_⟩
      exact (congrArg (fun t : 𝟙_ (SchemeOver k) ⟶ U.val.X ↦
        t.left (IsLocalRing.closedPoint k)) hprod).trans (sectionOfClosedPoint_apply _ _ _)
    · rintro _ ⟨w, rfl⟩
      let Y := H.group.X ⊗ S.group.X
      let j := fst H.group.X S.group.X
      let d := snd H.group.X S.group.X
      have hh : (d ≫ S.inclusion.hom.hom) • (toUnit Y ≫ x) = toUnit Y ≫ x :=
        (P.representsStabilizer Y _).mpr
          ⟨d ≫ D.inclusion.hom.hom, Category.assoc _ _ _⟩
      have he : m ≫ q = j ≫ orbitMap b x := by
        rw [orbitMap_restrict, ← Category.assoc, orbitMap_comp, orbitMap_comp]
        change ((j ≫ H.inclusion.hom.hom) * (d ≫ S.inclusion.hom.hom)) • (toUnit Y ≫ x) = _
        rw [mul_smul, hh]
      refine ⟨j.left w, ?_⟩
      exact congrArg (fun t : Y ⟶ X ↦ t.left w) he.symm
  have hclosed : IsClosed (i.left ⁻¹' C) := by
    letI := P.flat
    letI := P.finitePresentation
    letI := P.surjective
    apply (P.projection.left.isOpenMap.isQuotientMap P.projection.left.continuous
      P.projection.left.surjective).isCoinducing.isClosed_preimage.mp
    rw [← Set.preimage_comp]
    change IsClosed ((P.projection ≫ i).left ⁻¹' C)
    rw [hi, hpre]
    exact hm
  obtain ⟨z, rfl⟩ := (orbitPresentation_range P).symm ▸ hy
  letI : IsOpenImmersion P.openInClosure.left := P.isOpen
  letI : IsPreimmersion i.left := by
    change IsPreimmersion (P.openInClosure.left ≫ (orbitMap a x).left.imageι)
    infer_instance
  have himage : i.left '' (i.left ⁻¹' C) = C := Set.image_preimage_eq_of_subset hC
  have hclosure : z ∈ closure (i.left ⁻¹' C) := by
    rw [i.left.isEmbedding.isInducing.closure_eq_preimage_closure_image, himage]
    exact hyC
  rw [hclosed.closure_eq] at hclosure
  exact hclosure

private theorem tensorUnit_toUnit : toUnit (𝟙_ (SchemeOver k)) = 𝟙 (𝟙_ (SchemeOver k)) :=
  (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _

private theorem rational_orbitMap {G : GroupScheme k} {X : SchemeOver k}
    (a : ModObj G.X X) (x : 𝟙_ (SchemeOver k) ⟶ X) (g : 𝟙_ (SchemeOver k) ⟶ G.X) :
    letI := a
    g ≫ orbitMap a x = g • x := by
  letI := a
  rw [orbitMap_comp, tensorUnit_toUnit, Category.id_comp]

private theorem mul_quotient_action {G : GroupScheme k} {B : ClosedSubgroup G}
    (Q : QuotientEmbedding.Presentation B) (a : ModObj G.X Q.scheme)
    (ha : lift (fst G.X G.X) (snd G.X G.X ≫ Q.projection) ≫ a.smul = μ[G.X] ≫ Q.projection)
    {Y : SchemeOver k} (g h : Y ⟶ G.X) :
    letI := a
    g • (h ≫ Q.projection) = (g * h) ≫ Q.projection := by
  letI := a
  simpa only [Category.assoc, comp_lift_assoc, lift_fst, lift_snd_assoc, CategoryTheory.Hom.smul_def,
    CategoryTheory.Hom.mul_def] using congrArg (lift g h ≫ ·) ha

private theorem identity_orbitMap_eq_projection {G : GroupScheme k} {B : ClosedSubgroup G}
    (Q : QuotientEmbedding.Presentation B) (a : ModObj G.X Q.scheme)
    (ha : lift (fst G.X G.X) (snd G.X G.X ≫ Q.projection) ≫ a.smul = μ[G.X] ≫ Q.projection) :
    orbitMap a ((1 : 𝟙_ (SchemeOver k) ⟶ G.X) ≫ Q.projection) = Q.projection := by
  letI := a
  have h := orbitMap_comp a ((1 : 𝟙_ (SchemeOver k) ⟶ G.X) ≫ Q.projection) (𝟙 G.X)
  rw [Category.id_comp, ← Category.assoc, MonObj.comp_one, mul_quotient_action Q a ha, mul_one] at h
  exact h

private theorem projection_right_invariant {G : GroupScheme k} {B : ClosedSubgroup G}
    (Q : QuotientEmbedding.Presentation B) {Y : SchemeOver k}
    (g : Y ⟶ G.X) (h : Y ⟶ B.group.X) :
    (g * (h ≫ B.inclusion.hom.hom)) ≫ Q.projection = g ≫ Q.projection := by
  symm
  apply (projection_eq_iff Q _ _).mpr
  rw [← mul_assoc, inv_mul_cancel, one_mul]
  exact ⟨h, rfl⟩

open private restrictSubgroup compose_restrict local_maximal_of_ambient solvable_maximal_torus_iff
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate

private theorem borel_radical_has_open_orbit [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) (T L B : ClosedSubgroup G.val) (hT : IsMaximalTorus T)
    (hL : IsBorel L) (hTL : IsSubgroupOf T L) (hTB : IsSubgroupOf T B)
    (hprod : DenseRange (multiplyFactors L.inclusion B.inclusion).left)
    (Q : QuotientEmbedding.Presentation B) [IsProper Q.scheme.hom]
    (a : ModObj G.val.X Q.scheme)
    (ha : lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ Q.projection) ≫ a.smul =
      μ[G.val.X] ≫ Q.projection) :
    ∃ U : ClosedSubgroup L.group, Specs.GeometricTorusSplitting.IsUnipotentRadical (G := closedSubgroupAlgebraicGroup L) U ∧
      IsOpen (orbitSet (restrictGroupAction (U.inclusion ≫ L.inclusion) a)
        ((1 : 𝟙_ (SchemeOver k) ⟶ G.val.X) ≫ Q.projection)) := by
  obtain ⟨U, _, _, hU, _, _, _, hsplit⟩ := GeometricTorusSplitting.splitting
    (closedSubgroupAlgebraicGroup L) hL.1.1 hL.1.2.1 hL.1.2.2
  obtain ⟨s, hs⟩ := hTL
  obtain ⟨t, ht⟩ := hTB
  let T' := restrictSubgroup T L s hs
  have ht' : IsMaximalTorus T' :=
    local_maximal_of_ambient L T' ((compose_restrict T L s hs).symm ▸ hT)
  let recProduct := Specs.GeometricTorusSplitting.subgroupProduct U T'
  haveI : IsIso recProduct := (hsplit T').2
    ((solvable_maximal_torus_iff (closedSubgroupAlgebraicGroup L) T').mpr ht')
  let x := (1 : 𝟙_ (SchemeOver k) ⟶ G.val.X) ≫ Q.projection
  let Y := (U.group.X ⊗ T'.group.X) ⊗ B.group.X
  let u : Y ⟶ U.group.X := fst _ _ ≫ fst _ _
  let b : Y ⟶ B.group.X :=
    (fst _ _ ≫ snd U.group.X T'.group.X ≫ t.hom.hom) * snd _ _
  let e : Y ⟶ L.group.X ⊗ B.group.X := recProduct ⊗ₘ 𝟙 B.group.X
  let m := multiplyFactors L.inclusion B.inclusion
  let iU : U.group.X ⟶ L.group.X := U.inclusion.hom.hom
  have heProduct : recProduct =
      (fst U.group.X T'.group.X ≫ iU) * (snd U.group.X T'.group.X ≫ s.hom.hom) := rfl
  have hst : s.hom.hom ≫ L.inclusion.hom.hom = t.hom.hom ≫ B.inclusion.hom.hom :=
    congrArg (Grp.forget (SchemeOver k)).map (hs.trans ht.symm)
  have hmap : e ≫ m = (u ≫ (U.inclusion ≫ L.inclusion).hom.hom) * (b ≫ B.inclusion.hom.hom) := by
    simp only [e, m, multiplyFactors, MonObj.comp_mul, tensorHom_fst_assoc, tensorHom_snd_assoc,
      Category.id_comp, heProduct, MonObj.mul_comp, Category.assoc, hst, u, b, mul_assoc]
    rfl
  have hproj : e ≫ m ≫ Q.projection =
      u ≫ orbitMap (restrictGroupAction (U.inclusion ≫ L.inclusion) a) x := by
    rw [← Category.assoc, hmap, projection_right_invariant, orbitMap_restrict,
      identity_orbitMap_eq_projection Q a ha, Category.assoc]
  haveI : IsIso e := inferInstanceAs (IsIso (recProduct ⊗ₘ 𝟙 B.group.X))
  haveI : IsIso e.left := (Over.forget (Spec (CommRingCat.of k))).map_isIso e
  letI := Q.surjective
  have hd : DenseRange (e ≫ m ≫ Q.projection).left := by
    change Dense (Set.range ((⇑Q.projection.left ∘ ⇑m.left) ∘ ⇑e.left))
    rw [e.left.surjective.range_comp (⇑Q.projection.left ∘ ⇑m.left)]
    exact Q.projection.left.surjective.denseRange.comp hprod Q.projection.left.continuous
  let C := orbitSet (restrictGroupAction (U.inclusion ≫ L.inclusion) a) x
  have hdC : Dense C := by
    refine hd.mono ?_
    rw [hproj, Over.comp_left]
    change Set.range ((orbitMap (restrictGroupAction (U.inclusion ≫ L.inclusion) a) x).left ∘ u.left) ⊆ _
    exact Set.range_comp_subset_range _ _
  have hlc : IsLocallyClosed C :=
    orbit_locallyClosed (closedSubgroupAlgebraicGroup U) hU.1 _ _
  have ho : IsOpen C := by
    simpa only [coborder_eq_union_closure_compl, hdC.closure_eq, Set.compl_univ, Set.union_empty]
      using hlc.isOpen_coborder
  exact ⟨U, hU, ho⟩

private def translateAction {G : GroupScheme k} {X : SchemeOver k}
    (a : ModObj G.X X) (g : 𝟙_ (SchemeOver k) ⟶ G.X) : X ≅ X := by
  letI := a
  refine ⟨(toUnit X ≫ g) • (𝟙 X), (toUnit X ≫ g⁻¹) • (𝟙 X), ?_, ?_⟩
  · rw [ModObj.comp_smul, comp_toUnit_assoc, Category.comp_id, GrpObj.comp_inv, inv_smul_smul]
  · rw [ModObj.comp_smul, comp_toUnit_assoc, Category.comp_id, GrpObj.comp_inv, smul_inv_smul]

private theorem orbitMap_conjugate {G : GroupScheme k} {X : SchemeOver k}
    (a : ModObj G.X X) {U : ClosedSubgroup G} (g : 𝟙_ (SchemeOver k) ⟶ G.X)
    (x : 𝟙_ (SchemeOver k) ⟶ X) :
    letI := a
    orbitMap (restrictGroupAction (conjugate g U).inclusion a) (g • x) =
      orbitMap (restrictGroupAction U.inclusion a) x ≫ (translateAction a g).hom := by
  letI := a
  rw [orbitMap_restrict, orbitMap_restrict, orbitMap_comp, orbitMap_comp, conjugate_inclusion]
  change (U.inclusion.hom.hom ≫ (conjugation g).hom.hom) • (toUnit U.group.X ≫ (g • x)) =
    (U.inclusion.hom.hom • (toUnit U.group.X ≫ x)) ≫
      ((toUnit X ≫ g) • (𝟙 X))
  rw [conjugation_apply, ModObj.comp_smul, ModObj.comp_smul, comp_toUnit_assoc, Category.comp_id]
  simp only [mul_smul, inv_smul_smul]

private theorem orbitSet_translate {U : GroupScheme k} {X : SchemeOver k}
    (a : ModObj U.X X) (x : 𝟙_ (SchemeOver k) ⟶ X) (u : 𝟙_ (SchemeOver k) ⟶ U.X) :
    letI := a
    orbitSet a (u • x) = orbitSet a x := by
  letI := a
  let e := GrpObj.mulRight u
  have he : orbitMap a (u • x) = e.hom ≫ orbitMap a x := by
    rw [← Category.id_comp (orbitMap a (u • x)), orbitMap_comp, orbitMap_comp]
    change (𝟙 U.X) • (toUnit U.X ≫ (u • x)) =
      ((𝟙 U.X) * (toUnit U.X ≫ u)) • (toUnit U.X ≫ x)
    rw [ModObj.comp_smul, mul_smul]
  rw [orbitSet, he, Over.comp_left]
  haveI : IsIso e.hom.left := (Over.forget (Spec (CommRingCat.of k))).map_isIso e.hom
  exact e.hom.left.surjective.range_comp (orbitMap a x).left

private theorem orbit_meets_open [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    {X : SchemeOver k} (a : ModObj G.val.X X) (x : 𝟙_ (SchemeOver k) ⟶ X)
    {V : Set X.left} (ho : IsOpen V) {y : X.left} (hy : y ∈ closure (orbitSet a x)) (hyV : y ∈ V) :
    ∃ g : 𝟙_ (SchemeOver k) ⟶ G.val.X,
      (g ≫ orbitMap a x).left (IsLocalRing.closedPoint k) ∈ V := by
  let q := orbitMap a x
  obtain ⟨_, hx, w, rfl⟩ := mem_closure_iff.mp hy V ho hyV
  letI := G.property.2.1
  haveI : JacobsonSpace G.val.X.left := LocallyOfFiniteType.jacobsonSpace G.val.X.hom
  obtain ⟨p, hp, hc⟩ := nonempty_inter_closedPoints (show (q.left ⁻¹' V).Nonempty from ⟨w, hx⟩)
    (ho.preimage q.left.continuous).isLocallyClosed
  refine ⟨sectionOfClosedPoint G.val.X p hc, ?_⟩
  change q.left ((sectionOfClosedPoint G.val.X p hc).left (IsLocalRing.closedPoint k)) ∈ V
  rwa [sectionOfClosedPoint_apply]


private theorem restricted_smul {H G : GroupScheme k} {X Y : SchemeOver k}
    (f : H ⟶ G) (a : ModObj G.X X) (g : Y ⟶ H.X) (x : Y ⟶ X) :
    letI := restrictGroupAction f a
    g • x = (letI := a; (g ≫ f.hom.hom) • x) := by
  letI := a
  change lift g x ≫ (restrictGroupAction f a).smul = lift (g ≫ f.hom.hom) x ≫ a.smul
  simp only [restrictGroupAction_smul, lift_map_assoc, Category.comp_id]

private theorem fixedPoint_iff_fixedBy {G : GroupScheme k} {X : SchemeOver k}
    (a : ModObj G.X X) (T : ClosedSubgroup G) (x : 𝟙_ (SchemeOver k) ⟶ X) :
    IsFixedPoint a T x ↔ IsFixedBy (restrictGroupAction T.inclusion a).smul x := by
  letI := restrictGroupAction T.inclusion a
  rw [fixed_iff_sections x]
  constructor
  · intro h Y q g
    have hh := congrArg (g ≫ ·) h
    change g ≫ lift T.inclusion.hom.hom (toUnit T.group.X ≫ x) ≫ a.smul =
      g ≫ toUnit T.group.X ≫ x at hh
    rw [restricted_smul, toUnit_unique q (toUnit Y)]
    simpa only [Category.assoc, comp_lift_assoc, comp_toUnit_assoc, CategoryTheory.Hom.smul_def] using hh
  · intro h
    have hh := h (toUnit T.group.X) (𝟙 T.group.X)
    rw [restricted_smul, Category.id_comp] at hh
    exact hh

open private conjugateLe_iff from LinearAlgebraicGroups.Affine.Stabilizers

private theorem subgroup_in_conjugate_by_normalizer {G : GroupScheme k}
    (T L : ClosedSubgroup G) (hTL : IsSubgroupOf T L) (g : 𝟙_ (SchemeOver k) ⟶ G.X)
    (hg : Normalizes T.inclusion g) : IsSubgroupOf T (conjugate g L) := by
  have h := (normalizesIff k T.inclusion T.isClosedImmersion _ g).mp hg
  obtain ⟨b, hb⟩ := (conjugateLe_iff T.inclusion g⁻¹).mp h.2 T.group.X (toUnit _) (𝟙 _)
  have hSub : IsSubgroupOf (conjugate g⁻¹ T) T := by
    apply factor_group_through_subgroup T (conjugate g⁻¹ T).inclusion b
    rw [conjugate_inclusion]
    change b ≫ T.inclusion.hom.hom = T.inclusion.hom.hom ≫ (conjugation g⁻¹).hom.hom
    rw [conjugation_apply]
    simpa only [Category.id_comp] using hb
  have h' := conjugate_subgroupOf g (subgroupOf_trans hSub hTL)
  have he := conjugate_inv_cancel g⁻¹ T
  rw [inv_inv] at he
  rwa [he] at h'

private theorem borel_of_fixed_quotient [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    {B : ClosedSubgroup G.val} (hB : IsBorel B) (Q : QuotientEmbedding.Presentation B)
    (a : ModObj G.val.X Q.scheme)
    (ha : lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ Q.projection) ≫ a.smul =
      μ[G.val.X] ≫ Q.projection)
    (H : ClosedSubgroup G.val)
    (hf : ∀ x : 𝟙_ (SchemeOver k) ⟶ Q.scheme, IsFixedBy (restrictGroupAction H.inclusion a).smul x)
    (B' : ClosedSubgroup G.val) (hB' : IsBorel B') :
    IsSubgroupOf H B' := by
  obtain ⟨g, e, he⟩ := LinearAlgebraicGroups.GeometricBorelConjugacy.borelsConjugate G hs hc B B' hB hB'
  let x := g ≫ Q.projection
  let c := toUnit H.group.X ≫ g
  letI := restrictGroupAction H.inclusion a
  have hfix := ((fixed_iff_sections x).mp (hf x)) (toUnit H.group.X) (𝟙 H.group.X)
  rw [restricted_smul] at hfix
  letI := a
  change ((𝟙 H.group.X) ≫ H.inclusion.hom.hom) • (toUnit H.group.X ≫ g ≫ Q.projection) =
    toUnit H.group.X ≫ g ≫ Q.projection at hfix
  rw [← Category.assoc (toUnit H.group.X) g, Category.id_comp, mul_quotient_action Q a ha] at hfix
  obtain ⟨f, hfx⟩ := (projection_eq_iff Q c (H.inclusion.hom.hom * c)).mp hfix.symm
  change f ≫ B.inclusion.hom.hom = c⁻¹ * (H.inclusion.hom.hom * c) at hfx
  have hH : IsSubgroupOf (conjugate g⁻¹ H) B := by
    apply factor_group_through_subgroup B (conjugate g⁻¹ H).inclusion f
    rw [conjugate_inclusion]
    change f ≫ B.inclusion.hom.hom = H.inclusion.hom.hom ≫ (conjugation g⁻¹).hom.hom
    rw [conjugation_apply]
    simpa only [c, GrpObj.comp_inv, inv_inv, mul_assoc] using hfx
  have hconj : IsSubgroupOf (conjugate g B) B' :=
    ⟨e.hom, Grp.hom_ext _ _ (he.trans (conjugation_apply g B.inclusion.hom.hom).symm)⟩
  have h' := conjugate_subgroupOf g hH
  have hh := conjugate_inv_cancel g⁻¹ H
  rw [inv_inv] at hh
  rw [hh] at h'
  exact subgroupOf_trans h' hconj

set_option maxHeartbeats 2400000 in
private theorem lies_in_all_borels [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (T : ClosedSubgroup G.val) (hT : IsMaximalTorus T)
    (fixed : BorelQuotientFixedPoints.{u}) (quotient : QuotientByCentralizer.{u})
    (H : ClosedSubgroup G.val) (hHs : Smooth H.group.X.hom) (hHc : ConnectedSpace H.group.X.left)
    (hHu : IsUnipotent (closedSubgroupAlgebraicGroup H))
    (hH : ∀ K ∈ borelUnipotentRadicals T, IsSubgroupOf H K) :
    ∀ B : ClosedSubgroup G.val, IsBorel B → IsSubgroupOf H B := by
  letI := hs
  letI := hc
  have hTs := torus_has_split_coordinates T hT.1
  obtain ⟨N, _, _, _, _, _, hN, _, _, _, _, _, _, hSplit, _⟩ := quotient G hs hc T hT.1
  obtain ⟨W⟩ := hSplit hTs
  obtain ⟨L, B, hL, hB, hTL, hTB, hProd⟩ :=
    borels_with_dense_product G T hT hTs fixed N hN W.faithfulWeights
  obtain ⟨Q⟩ := (HomogeneousQuotient.homogeneousQuotient k G B).1
  haveI := borel_quotient_proper G hs hc B hB Q
  obtain ⟨a, ha, _, hRep, _, htrans⟩ := fixed G hs hc T B hT hB hTB N hN Q
  letI := a
  let X := Q.scheme
  let x₀ : 𝟙_ (SchemeOver k) ⟶ X := (1 : 𝟙_ (SchemeOver k) ⟶ G.val.X) ≫ Q.projection
  have hx₀ : IsFixedPoint a T x₀ := (hRep x₀).mpr
    ⟨1, by rw [← Category.assoc, MonObj.one_comp]⟩
  obtain ⟨V, hV, hVopen⟩ := borel_radical_has_open_orbit G T L B hT hL hTL hTB hProd Q a ha
  let K := closedSubgroupAlgebraicGroup T
  let aT := restrictGroupAction T.inclusion a
  obtain ⟨hts, htc, htSol⟩ := torus_smooth_connected_solvable K hT.1
  have chart (y : 𝟙_ (SchemeOver k) ⟶ X) (hy : IsFixedPoint a T y) :
      ∃ (D : ClosedSubgroup G.val) (U : ClosedSubgroup D.group),
        IsBorel D ∧ IsSubgroupOf T D ∧
        Specs.GeometricTorusSplitting.IsUnipotentRadical (G := closedSubgroupAlgebraicGroup D) U ∧
        IsOpen (orbitSet (restrictGroupAction (U.inclusion ≫ D.inclusion) a) y) := by
    obtain ⟨n, hn⟩ := htrans x₀ y hx₀ hy
    let g := n ≫ N.inclusion.hom.hom
    have hnorm := (hN _ g).mpr ⟨n, rfl⟩
    let D := conjugate g L
    refine ⟨D, V, borel_conjugate g hL, subgroup_in_conjugate_by_normalizer T L hTL g hnorm, hV, ?_⟩
    have hincl : V.inclusion ≫ D.inclusion = (conjugate g (subgroupOfSubgroup L V)).inclusion := by
      change V.inclusion ≫ L.inclusion ≫ conjugation g = (V.inclusion ≫ L.inclusion) ≫ conjugation g
      exact (Category.assoc _ _ _).symm
    have hny : g • x₀ = y := hn
    rw [hincl, ← hny, orbitSet, orbitMap_conjugate, Over.comp_left]
    change IsOpen (Set.range ((translateAction a g).hom.left ∘
      (orbitMap (restrictGroupAction (V.inclusion ≫ L.inclusion) a) x₀).left))
    rw [Set.range_comp]
    haveI : IsIso (translateAction a g).hom.left :=
      (Over.forget (Spec (CommRingCat.of k))).map_isIso (translateAction a g).hom
    exact (translateAction a g).hom.left.homeomorph.isOpenMap _ hVopen
  have cover (z : 𝟙_ (SchemeOver k) ⟶ X) :
      ∃ (w : 𝟙_ (SchemeOver k) ⟶ X) (D : ClosedSubgroup G.val) (U : ClosedSubgroup D.group),
        IsBorel D ∧ IsSubgroupOf T D ∧
        Specs.GeometricTorusSplitting.IsUnipotentRadical (G := closedSubgroupAlgebraicGroup D) U ∧
        IsOpen (orbitSet (restrictGroupAction (U.inclusion ≫ D.inclusion) a) w) ∧
        z.left (IsLocalRing.closedPoint k) ∈ orbitSet (restrictGroupAction (U.inclusion ≫ D.inclusion) a) w := by
    obtain ⟨w, hwcl, hwfix⟩ := fixed_point_in_orbit_closure K hts htc htSol aT z
    have hwT := (fixedPoint_iff_fixedBy a T w).mpr hwfix
    obtain ⟨D, U, hD, hTD, hU, ho⟩ := chart w hwT
    let A := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup D) U
    let aU := restrictGroupAction (U.inclusion ≫ D.inclusion) a
    have hw : w.left (IsLocalRing.closedPoint k) ∈ orbitSet aU w := by
      apply (SmoothOrbit.geometricOrbitLifts k A X aU w w).mpr
      exact ⟨1, (rational_orbitMap aU w 1).trans (by letI := aU; exact one_smul _ _)⟩
    obtain ⟨t, ht⟩ := orbit_meets_open K aT z ho hwcl hw
    obtain ⟨u, hu⟩ := (SmoothOrbit.geometricOrbitLifts k A X aU w (t ≫ orbitMap aT z)).mp ht
    obtain ⟨s, hs⟩ := hTD
    let tD := t ≫ s.hom.hom
    let tG := t ≫ T.inclusion.hom.hom
    have htG : tD ≫ D.inclusion.hom.hom = tG := by
      rw [Category.assoc]
      exact congrArg (fun f : T.group ⟶ G.val ↦ t ≫ f.hom.hom) hs
    obtain ⟨v, hv⟩ := normalSubgroup_conjugate_sections hU.2.2.1 tD⁻¹ u
    have hvG : v ≫ (U.inclusion ≫ D.inclusion).hom.hom =
        tG⁻¹ * (u ≫ (U.inclusion ≫ D.inclusion).hom.hom) * tG := by
      change v ≫ U.inclusion.hom.hom ≫ D.inclusion.hom.hom = _
      rw [inv_inv] at hv
      rw [← Category.assoc, hv]
      simp only [MonObj.mul_comp, GrpObj.inv_comp, htG, Category.assoc]
      rfl
    have htw : tG • w = w := by
      have h := ((fixed_iff_sections (act := aT) w).mp hwfix) (𝟙 _) t
      rw [Category.id_comp] at h
      exact (restricted_smul T.inclusion a t w).symm.trans h
    have hu' : (u ≫ (U.inclusion ≫ D.inclusion).hom.hom) • w = tG • z := by
      have h₁ := (rational_orbitMap aU w u).trans (restricted_smul (U.inclusion ≫ D.inclusion) a u w)
      have h₂ := (rational_orbitMap aT z t).trans (restricted_smul T.inclusion a t z)
      exact h₁.symm.trans (hu.trans h₂)
    refine ⟨w, D, U, hD, ⟨s, hs⟩, hU, ho, ?_⟩
    apply (SmoothOrbit.geometricOrbitLifts k A X aU w z).mpr
    refine ⟨v, ?_⟩
    refine ((rational_orbitMap aU w v).trans (restricted_smul (U.inclusion ≫ D.inclusion) a v w)).trans ?_
    rw [hvG, mul_smul, mul_smul, htw, hu', inv_smul_smul]
  apply borel_of_fixed_quotient G hs hc hB Q a ha H
  intro x
  let J := closedSubgroupAlgebraicGroup H
  let aH := restrictGroupAction H.inclusion a
  have hsol := unipotent_solvable J hHs hHc hHu
  obtain ⟨y, hycl, hyfix⟩ := fixed_point_in_orbit_closure J hHs hHc hsol aH x
  obtain ⟨w, D, U, hD, hTD, hU, ho, hy⟩ := cover y
  let A := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup D) U
  let U' := subgroupOfSubgroup D U
  let aU := restrictGroupAction U'.inclusion a
  have hUR : IsUnipotentRadical (closedSubgroupAlgebraicGroup D) U :=
    ⟨⟨hU.1, hU.2.1, hU.2.2.1⟩, hU.2.2.2.1, fun V _ hV ↦ hU.2.2.2.2 V hV⟩
  obtain ⟨f, hf⟩ := hH U' ⟨D, U, hD, hTD, hUR, rfl⟩
  let F : ClosedSubgroup A.val := ⟨H.group, f, factor_closed hf⟩
  let b := restrictGroupAction F.inclusion aU
  have hmaps (p : 𝟙_ (SchemeOver k) ⟶ X) : orbitMap b p = orbitMap aH p := by
    rw [orbitMap_restrict, orbitMap_restrict, orbitMap_restrict, ← Category.assoc]
    exact congrArg (fun t : H.group ⟶ G.val ↦ t.hom.hom ≫ orbitMap a p) hf
  obtain ⟨j, hj⟩ := orbit_meets_open J aH x ho hycl hy
  let z := j ≫ orbitMap aH x
  obtain ⟨p, hp⟩ := (SmoothOrbit.geometricOrbitLifts k A X aU w z).mp hj
  let u : 𝟙_ (SchemeOver k) ⟶ U'.group.X := p
  have hu : u ≫ orbitMap aU w = j ≫ orbitMap aH x := hp
  letI : ModObj U'.group.X X := aU
  have hJ : j ≫ orbitMap aH x = (j ≫ f.hom.hom) ≫ orbitMap aU x := by
    rw [← hmaps x, orbitMap_restrict]
    exact (Category.assoc _ _ _).symm
  have hu' : u • w = (j ≫ f.hom.hom) • x :=
    (rational_orbitMap aU w u).symm.trans (hu.trans (hJ.trans (rational_orbitMap aU x _)))
  have hx : ((j ≫ f.hom.hom)⁻¹ * u) • w = x := by
    rw [mul_smul, hu', inv_smul_smul]
  have hwEq : orbitSet aU x = orbitSet aU w :=
    (congrArg (orbitSet aU) hx).symm.trans (orbitSet_translate aU w _)
  have hyU : y.left (IsLocalRing.closedPoint k) ∈ orbitSet aU x := hwEq.symm ▸ hy
  have hOrbitSet : orbitSet b x = orbitSet aH x :=
    congrArg (fun o : H.group.X ⟶ X ↦ Set.range o.left) (hmaps x)
  have hyc : y.left (IsLocalRing.closedPoint k) ∈ closure (orbitSet b x) := by
    rw [hOrbitSet]
    exact hycl
  have hmem : y.left (IsLocalRing.closedPoint k) ∈ orbitSet b x :=
    orbit_closed_inside_unipotent_orbit A hU.1 hU.2.2.2.1 F hHs aU x hyU hyc
  have hmem' : y.left (IsLocalRing.closedPoint k) ∈ orbitSet aH x := by
    rw [← hOrbitSet]
    exact hmem
  obtain ⟨r, hr⟩ := (SmoothOrbit.geometricOrbitLifts k J X aH x y).mp hmem'
  let h : 𝟙_ (SchemeOver k) ⟶ H.group.X := r
  have hh : h ≫ orbitMap aH x = y := hr
  letI : ModObj H.group.X X := aH
  have hh' : h • x = y := (rational_orbitMap aH x h).symm.trans hh
  have hhfix := ((fixed_iff_sections y).mp hyfix) (𝟙 _) h⁻¹
  rw [Category.id_comp] at hhfix
  have hxy : x = y := by
    calc
      x = h⁻¹ • (h • x) := (inv_smul_smul h x).symm
      _ = h⁻¹ • y := congrArg (h⁻¹ • ·) hh'
      _ = y := hhfix
  exact hxy.symm ▸ hyfix

theorem unipotentRadicalFromBorelIntersection_conditional
    (fixed : BorelQuotientFixedPoints.{u}) (_ : NormalTorusCentral.{u})
    (quotient : QuotientByCentralizer.{u}) : UnipotentRadicalFromBorelIntersection.{u} := by
  intro k _ _ G hs hc T hT
  exact unipotentIntersection_of_borel_containment G hs hc T hT
    (lies_in_all_borels G hs hc T hT fixed quotient)

end
end LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection

universe v8_closure_a37886da1db0ad22_u0
theorem _root_.«LinearAlgebraicGroups».«Reductive».«UnipotentRadicalIntersection».«solvableRadicalFromBorelIntersection» : _root_.«LinearAlgebraicGroups».«Specs».«UnipotentRadicalIntersection».«SolvableRadicalFromBorelIntersection».{v8_closure_a37886da1db0ad22_u0} :=
  @_root_.«LinearAlgebraicGroups».«Reductive».«UnipotentRadicalIntersection».«solvableRadicalFromBorelIntersection_conditional».{v8_closure_a37886da1db0ad22_u0} (@_root_.«LinearAlgebraicGroups».«NormalizerLatticeAction».«borelQuotientFixedPoints».{v8_closure_a37886da1db0ad22_u0}) (@_root_.«LinearAlgebraicGroups».«NormalizerLatticeAction».«normalTorusCentral».{v8_closure_a37886da1db0ad22_u0}) (@_root_.«LinearAlgebraicGroups».«NormalizerLatticeAction».«quotientByCentralizer».{v8_closure_a37886da1db0ad22_u0})
theorem _root_.«LinearAlgebraicGroups».«Reductive».«UnipotentRadicalIntersection».«unipotentOrbitsClosed» : _root_.«LinearAlgebraicGroups».«Specs».«UnipotentRadicalIntersection».«UnipotentOrbitsClosed».{v8_closure_a37886da1db0ad22_u0} :=
  @_root_.«LinearAlgebraicGroups».«Reductive».«UnipotentRadicalIntersection».«unipotentOrbitsClosed_conditional».{v8_closure_a37886da1db0ad22_u0} (@_root_.«LinearAlgebraicGroups».«NormalizerLatticeAction».«borelQuotientFixedPoints».{v8_closure_a37886da1db0ad22_u0}) (@_root_.«LinearAlgebraicGroups».«NormalizerLatticeAction».«normalTorusCentral».{v8_closure_a37886da1db0ad22_u0}) (@_root_.«LinearAlgebraicGroups».«NormalizerLatticeAction».«quotientByCentralizer».{v8_closure_a37886da1db0ad22_u0})
theorem _root_.«LinearAlgebraicGroups».«Reductive».«UnipotentRadicalIntersection».«unipotentRadicalFromBorelIntersection» : _root_.«LinearAlgebraicGroups».«Specs».«UnipotentRadicalIntersection».«UnipotentRadicalFromBorelIntersection».{v8_closure_a37886da1db0ad22_u0} :=
  @_root_.«LinearAlgebraicGroups».«Reductive».«UnipotentRadicalIntersection».«unipotentRadicalFromBorelIntersection_conditional».{v8_closure_a37886da1db0ad22_u0} (@_root_.«LinearAlgebraicGroups».«NormalizerLatticeAction».«borelQuotientFixedPoints».{v8_closure_a37886da1db0ad22_u0}) (@_root_.«LinearAlgebraicGroups».«NormalizerLatticeAction».«normalTorusCentral».{v8_closure_a37886da1db0ad22_u0}) (@_root_.«LinearAlgebraicGroups».«NormalizerLatticeAction».«quotientByCentralizer».{v8_closure_a37886da1db0ad22_u0})
