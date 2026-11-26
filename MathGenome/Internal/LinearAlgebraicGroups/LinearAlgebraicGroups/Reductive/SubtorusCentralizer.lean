import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.SubtorusCentralizer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterDynamics
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
import Batteries.Tactic.OpenPrivate
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj MonoidAlgebra

universe u

namespace LinearAlgebraicGroups.Reductive.SubtorusCentralizer

open LinearAlgebraicGroups.Specs
open Specs.SubtorusCentralizer
open Specs.UnipotentRadicalIntersection
open Specs.GeometricBorelConjugacy (IsBorel IsSmoothConnectedSolvable subgroupOfSubgroup)
open Specs.GeometricRadicals (IsMaximalTorus IsReductive IsTorus IsUnipotentRadical
  baseChangedSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf IsSolvable)
open Specs.Unipotent (closedSubgroupAlgebraicGroup baseChangedAlgebraicGroup IsUnipotent)
open Specs.QuotientEmbedding (Presentation)

open private mono_over from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private factor_group_through_subgroup subgroupOf_trans
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private factor_closed solvable_iff_sections rationalSections
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private iso_of_same_subgroup from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

variable {k : Type u} [Field k] {G : GroupScheme k}

private theorem subgroupOf_of_sections {A B : ClosedSubgroup G}
    (h : A.inclusion.hom.hom ∈ SubgroupSections B A.group.X) : IsSubgroupOf A B := by
  obtain ⟨i, hi⟩ := h
  exact factor_group_through_subgroup B A.inclusion i hi

private theorem sections_of_subgroupOf {A B : ClosedSubgroup G} (h : IsSubgroupOf A B)
    {Y : SchemeOver k} {y : Y ⟶ G.X} (hy : y ∈ SubgroupSections A Y) :
    y ∈ SubgroupSections B Y := by
  obtain ⟨j, hj⟩ := h
  obtain ⟨a, ha⟩ := hy
  refine ⟨a ≫ j.hom.hom, ?_⟩
  have hj' := congrArg (fun f : A.group ⟶ G ↦ f.hom.hom) hj
  change j.hom.hom ≫ B.inclusion.hom.hom = A.inclusion.hom.hom at hj'
  change a ≫ A.inclusion.hom.hom = y at ha
  change (a ≫ j.hom.hom) ≫ B.inclusion.hom.hom = y
  rw [Category.assoc, hj', ha]

private theorem centralizer_geometry (A : AffineAlgebraicGroup k)
    (hs : Smooth A.val.X.hom) (hc : ConnectedSpace A.val.X.left)
    (S C : ClosedSubgroup A.val) (hS : IsTorus S.group) (hC : IsCentralizer S C) :
    Smooth C.group.X.hom ∧ GeometricallyConnected C.group.X.hom := by
  letI := hs
  letI := hc
  obtain ⟨D, hD, hd, hdc, _⟩ := CocharacterDynamics.torusCentralizer A S hS
  obtain ⟨e⟩ := iso_of_same_subgroup C D hC hD
  have he : e.hom.left ≫ D.group.X.hom = C.group.X.hom := Over.w e.hom
  haveI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have hp : IsPullback e.hom.left C.group.X.hom D.group.X.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using he⟩
  exact ⟨MorphismProperty.of_isPullback hp hd, MorphismProperty.of_isPullback hp hdc⟩

private theorem centralizes_through_closed_subgroup {H : GroupScheme k}
    (B : ClosedSubgroup G) (l : H ⟶ B.group) {Y : SchemeOver k}
    (b : Y ⟶ B.group.X) :
    Centralizes l b ↔ Centralizes (l ≫ B.inclusion) (b ≫ B.inclusion.hom.hom) := by
  letI : Mono B.inclusion.hom.hom := mono_over _ B.isClosedImmersion
  unfold Centralizes conjugateFamily
  rw [← cancel_mono B.inclusion.hom.hom]
  simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]
  rfl

private theorem centralizer_intersection [IsAlgClosed k] (A : AffineAlgebraicGroup k)
    {S T C B : ClosedSubgroup A.val} (hS : IsTorus S.group)
    (hst : IsSubgroupOf S T) (htb : IsSubgroupOf T B) (hb : IsBorel B)
    (hC : IsCentralizer S C) :
    ∃ D : ClosedSubgroup C.group, IsCentralizerIntersection C B D ∧
      IsSmoothConnectedSolvable D := by
  let B' := closedSubgroupAlgebraicGroup B
  obtain ⟨l, hl⟩ := subgroupOf_trans hst htb
  let S' : ClosedSubgroup B'.val := ⟨S.group, l, factor_closed hl⟩
  letI : Smooth B'.val.X.hom := hb.1.1
  letI : ConnectedSpace B'.val.X.left := hb.1.2.1
  obtain ⟨E, hE, he, hec, _⟩ := CocharacterDynamics.torusCentralizer B' S' hS
  let F := subgroupOfSubgroup B E
  have hlift : IsSubgroupOf F C := by
    apply subgroupOf_of_sections
    apply (hC _ _).mp
    rw [← hl]
    exact (centralizes_through_closed_subgroup B l E.inclusion.hom.hom).mp
      ((hE _ _).mpr ⟨𝟙 _, Category.id_comp _⟩)
  obtain ⟨j, hj⟩ := hlift
  let D : ClosedSubgroup C.group := ⟨E.group, j, factor_closed hj⟩
  have heconn : ConnectedSpace E.group.X.left := by
    letI := hec
    exact GeometricallyConnected.connectedSpace_of_subsingleton E.group.X.hom
  refine ⟨D, ?_, he, heconn, ?_⟩
  · intro Y y
    have hD : (subgroupOfSubgroup C D).inclusion = F.inclusion := hj
    change (∃ d : Y ⟶ E.group.X, d ≫ (subgroupOfSubgroup C D).inclusion.hom.hom = y) ↔ _
    rw [hD]
    change y ∈ SubgroupSections F Y ↔ _
    constructor
    · intro hy H hH
      rcases Set.mem_insert_iff.mp hH with rfl | heq
      · exact sections_of_subgroupOf ⟨j, hj⟩ hy
      · obtain rfl := Set.mem_singleton_iff.mp heq
        exact sections_of_subgroupOf ⟨E.inclusion, rfl⟩ hy
    · intro hy
      obtain ⟨b, hb⟩ := hy B (by simp)
      change b ≫ B.inclusion.hom.hom = y at hb
      have hc := (hC Y y).mpr (hy C (by simp))
      rw [← hb, ← hl, ← centralizes_through_closed_subgroup B l b] at hc
      obtain ⟨e, heq⟩ := (hE Y b).mp hc
      exact ⟨e, by change e ≫ E.inclusion.hom.hom ≫ B.inclusion.hom.hom = y
                   rw [← Category.assoc, heq, hb]⟩
  · haveI : Group.IsSolvable (rationalSections B'.val) :=
      (solvable_iff_sections B' hb.1.1 hb.1.2.1).mp hb.1.2.2
    haveI : Mono E.inclusion.hom.hom := mono_over _ E.isClosedImmersion
    let f : rationalSections E.group →* rationalSections B'.val :=
      IsMonHom.monoidHom E.inclusion.hom.hom (𝟙_ (SchemeOver k))
    exact (solvable_iff_sections (closedSubgroupAlgebraicGroup (G := B') E) he heconn).mpr
      (Group.isSolvable_of_isSolvable_injective (f := f)
        (fun _ _ h ↦ (cancel_mono E.inclusion.hom.hom).mp h))

open private subgroupQuotientAction fixed_subgroup_conjugate rationalLift innerIso
  innerMap comp_innerMap transportSubgroup borel_transport monHom_of_factor_subgroup
  rightTranslation closed_flag_quotient_proper proper_of_conjugate_quotient
  quotientAct quotientAct_comp quotientAct_projection
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper
open private borel_of_containing_borel
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

private theorem borel_of_proper_quotient [IsAlgClosed k] (A : AffineAlgebraicGroup k)
    (hs : Smooth A.val.X.hom) (hc : ConnectedSpace A.val.X.left)
    (D : ClosedSubgroup A.val) (hD : IsSmoothConnectedSolvable D)
    (P : Presentation D) (hp : IsProper P.scheme.hom) : IsBorel D := by
  obtain ⟨B, hB⟩ := GeometricBorelConjugacy.borelExists A hs hc
  have hn : Nonempty P.scheme.left :=
    ⟨(η[A.val.X] ≫ P.projection).left (IsLocalRing.closedPoint k)⟩
  obtain ⟨Z, i, _, hi, ⟨z⟩⟩ :=
    BorelFixedPoint.overAlgClosed (closedSubgroupAlgebraicGroup B) P.scheme
      (subgroupQuotientAction (B := B) P) hB.1.1 hB.1.2.1 hB.1.2.2 hp hn
  obtain ⟨g, hg⟩ := rationalLift P.projection P.surjective
    (by letI := P.finitePresentation; infer_instance) (z ≫ i)
  have hz := (hi _ (z ≫ i)).mpr ⟨z, rfl⟩
  rw [← hg] at hz
  obtain ⟨b, hb⟩ := fixed_subgroup_conjugate P g hz
  let e := innerIso g⁻¹
  apply borel_of_containing_borel (A := transportSubgroup B e) (borel_transport hB e) hD
  apply monHom_of_factor_subgroup b e
  change b ≫ D.inclusion.hom.hom = B.inclusion.hom.hom ≫ (innerMap g⁻¹).hom.hom
  rw [comp_innerMap, GrpObj.comp_inv, inv_inv]
  exact hb

private theorem centralizerBorel_of_fixedLocusOrbits
    (orbits : FixedLocusOrbits.{u}) : CentralizerBorel.{u} := by
  intro k _ _ A hs hc T S ht hS hst C hC B hb htb
  obtain ⟨D, hD, hDsol⟩ := centralizer_intersection A hS hst htb hb hC
  obtain ⟨Q⟩ := (HomogeneousQuotient.homogeneousQuotient k A B).1
  obtain ⟨P⟩ :=
    (HomogeneousQuotient.homogeneousQuotient k (closedSubgroupAlgebraicGroup C) D).1
  obtain ⟨a, Z, i, b, _, _, _, _, _, _, h⟩ := orbits A hs hc T S ht hS hst C hC B hb htb Q
  obtain ⟨z, O, e, _, _⟩ := h D hD P
  haveI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  haveI : IsProper O.scheme.hom := O.proper
  have hp : IsProper P.scheme.hom := by rw [← Over.w e.hom]; infer_instance
  obtain ⟨hCs, hCc⟩ := centralizer_geometry A hs hc S C hS hC
  letI := hCc
  exact ⟨D, hD, borel_of_proper_quotient (closedSubgroupAlgebraicGroup C) hCs
    (GeometricallyConnected.connectedSpace_of_subsingleton C.group.X.hom) D hDsol P hp⟩

open private splitSolvable_of_additiveSeries from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.BorelFixedPoint
open private affineBaseTerminal from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SplitFixedPoint
open private split_solvable_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria

private theorem solvable_of_smooth_connected_unipotent [IsAlgClosed k] (A : AffineAlgebraicGroup k)
    (hs : Smooth A.val.X.hom) (hc : ConnectedSpace A.val.X.left) (hu : IsUnipotent A) :
    IsSolvable A.val := by
  obtain ⟨n, S, _, _, hS⟩ := Unipotent.perfectFieldSplitness A hs hc hu
  have hsplit := splitSolvable_of_additiveSeries (H := A) S hS (Iso.refl _)
  let r := CommAlgCat.of k k
  let t : (testSpec k).obj (op r) ≅ 𝟙_ (SchemeOver k) :=
    (affineBaseTerminal k).uniqueUpToIso (isTerminalTensorUnit (C := SchemeOver k))
  let f : rationalSections A.val →* Points A.val.X r :=
    { toFun := fun x ↦ t.hom ≫ x
      map_one' := MonObj.comp_one _
      map_mul' := fun x y ↦ MonObj.comp_mul _ x y }
  letI := split_solvable_points hsplit r
  exact (solvable_iff_sections A hs hc).mpr (Group.isSolvable_of_isSolvable_injective
    (f := f) (fun x y h ↦ (cancel_epi t.hom).mp
      (show t.hom ≫ x = t.hom ≫ y from h)))

/-- A map from a reduced scheme factors through a closed subscheme if its
underlying image lies in that closed subscheme. -/
private theorem factors_of_range_subset {X Y Z : SchemeOver k} [IsReduced X.left]
    (f : X ⟶ Z) (i : Y ⟶ Z) (hi : IsClosedImmersion i.left)
    (h : Set.range f.left ⊆ Set.range i.left) : ∃ j : X ⟶ Y, j ≫ i = f := by
  let P := pullback f i
  let p : P ⟶ X := pullback.fst f i
  let q : P ⟶ Y := pullback.snd f i
  have hp : IsPullback p.left q.left f.left i.left :=
    (IsPullback.of_hasPullback f i).map (Over.forget _)
  letI : IsClosedImmersion p.left := MorphismProperty.of_isPullback hp.flip hi
  letI : Surjective p.left := ⟨fun x ↦ by
    obtain ⟨y, hy⟩ := h ⟨x, rfl⟩
    obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback hp x y hy.symm
    exact ⟨w, hw⟩⟩
  haveI : IsIso ((Over.forget (Spec (CommRingCat.of k))).map p) :=
    isIso_of_isClosedImmersion_of_surjective p.left
  haveI : IsIso p := isIso_of_reflects_iso p (Over.forget (Spec (CommRingCat.of k)))
  refine ⟨inv p ≫ q, ?_⟩
  rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

private theorem factors_reduced_component {H A : GroupScheme k}
    (J : ClosedSubgroup H) (hJ : GeometricBorelConjugacy.IsReducedIdentityComponent J)
    (f : A ⟶ H) (hs : Smooth A.X.hom) (hc : ConnectedSpace A.X.left) :
    ∃ j : A ⟶ J.group, j ≫ J.inclusion = f := by
  letI := hc
  letI := hs
  letI := isReduced_of_smooth_over_field A.X.hom
  have hr : Set.range f.hom.hom.left ⊆ Set.range J.inclusion.hom.hom.left := by
    rw [hJ.2]
    apply (isConnected_range f.hom.hom.left.continuous).subset_connectedComponent
    refine ⟨η[A.X].left (IsLocalRing.closedPoint k), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨j, hj⟩ := factors_of_range_subset f.hom.hom J.inclusion.hom.hom J.isClosedImmersion hr
  exact factor_group_through_subgroup J f j hj

private theorem unipotentRadicalInclusion_of_centralizerBorel
    (borel : CentralizerBorel.{u}) (solvableIntersection : SolvableRadicalFromBorelIntersection.{u})
    (unipotentIntersection : UnipotentRadicalFromBorelIntersection.{u}) :
    UnipotentRadicalInclusion.{u} := by
  intro k _ _ A hs hc T S ht hS hst C hC U R hU hR
  obtain ⟨I, J, hI, hJ, hrad⟩ := unipotentIntersection A hs hc T ht
  have hin : IsSubgroupOf (subgroupOfSubgroup C U) I := by
    apply subgroupOf_of_sections
    apply (hI _ _).mpr
    intro H hH
    obtain ⟨B, N, hB, hTB, hN, rfl⟩ := hH
    obtain ⟨D, hD, hDB⟩ := borel A hs hc T S ht hS hst C hC B hB hTB
    obtain ⟨M, K, hM, _, hK⟩ :=
      solvableIntersection (closedSubgroupAlgebraicGroup C)
        (centralizer_geometry A hs hc S C hS hC).1
        (by
          letI := (centralizer_geometry A hs hc S C hS hC).2
          exact GeometricallyConnected.connectedSpace_of_subsingleton C.group.X.hom)
    let U' := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup C) U
    have hUs : IsSolvable U.group := solvable_of_smooth_connected_unipotent U'
      (show Smooth U'.val.X.hom from hU.1.1)
      (show ConnectedSpace U'.val.X.left from hU.1.2.1) hU.2.1
    have hUM : IsSubgroupOf U M :=
      subgroupOf_trans (hK.2.2 U hU.1 hUs) ⟨K.inclusion, rfl⟩
    have hMD : IsSubgroupOf M D := by
      apply subgroupOf_of_sections
      apply (hM _ _).mp ?_ D hDB
      refine ⟨𝟙 M.group.X, ?_⟩
      change 𝟙 M.group.X ≫ M.inclusion.hom.hom = M.inclusion.hom.hom
      exact Category.id_comp _
    have hUB : IsSubgroupOf (subgroupOfSubgroup C U) B := by
      apply subgroupOf_of_sections
      apply (hD _ _).mp ?_ B (by simp)
      obtain ⟨f, hf⟩ := subgroupOf_trans hUM hMD
      exact ⟨f.hom.hom, congrArg (fun x : U.group ⟶ C.group ↦
        (x ≫ C.inclusion).hom.hom) hf⟩
    obtain ⟨f, hf⟩ := hUB
    let V : ClosedSubgroup B.group := ⟨U.group, f, factor_closed hf⟩
    let B' := closedSubgroupAlgebraicGroup B
    obtain ⟨L, _, _, hL, _, _⟩ := GeometricTorusSplitting.splitting B'
      hB.1.1 hB.1.2.1 hB.1.2.2
    have hLN : IsSubgroupOf L N :=
      hN.2.2 L ⟨hL.1, hL.2.1, hL.2.2.1⟩ hL.2.2.2.1
    obtain ⟨j, hj⟩ := subgroupOf_trans (hL.2.2.2.2 V hU.2.1) hLN
    refine ⟨j.hom.hom, ?_⟩
    exact congrArg (fun x : U.group ⟶ B.group ↦ (x ≫ B.inclusion).hom.hom) hj |>.trans
      (congrArg (fun x : U.group ⟶ A.val ↦ x.hom.hom) hf)
  obtain ⟨f, hf⟩ := hin
  obtain ⟨j, hj⟩ := factors_reduced_component J hJ f hU.1.1 hU.1.2.1
  exact subgroupOf_trans ⟨j, by change j ≫ J.inclusion ≫ I.inclusion = _
                                rw [← Category.assoc, hj, hf]⟩
    (hR.2.2 _ hrad.1 hrad.2.1)

open private baseChangeMapIsPullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient
open private groupPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private extendedGroupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open LinearAlgebraicGroups.CharacterDescent (extendedHopfFunctor extendedHopfTower)
open Specs.CharacterDescent (StandardLattice)
open Specs.DiagonalizableGroups (groupAlgebra)

private theorem torus_coordinates (A : AffineAlgebraicGroup k) (h : IsTorus A.val) :
    ∃ B : HopfAlgebraCategory k, Nonempty (specGroup B ≅ A.val) ∧
      Specs.CharacterDescent.IsTorus B := by
  obtain ⟨B, _, ⟨e⟩⟩ := groupPresentation A
  obtain ⟨E, _, _, _, r, ⟨t⟩⟩ := h
  exact ⟨B, ⟨e⟩, (GeometricRadicals.torusCoordinateComparison B).mp
    ⟨E, inferInstance, inferInstance, inferInstance, r, ⟨(groupBaseChange k E).mapIso e ≪≫ t⟩⟩⟩

private theorem torus_baseChange_algClosure (A : AffineAlgebraicGroup k) (h : IsTorus A.val) :
    IsTorus ((groupBaseChange k (AlgebraicClosure k)).obj A.val) := by
  let K := AlgebraicClosure k
  obtain ⟨B, ⟨e⟩, E, _, _, hsep, r, ⟨d⟩⟩ := torus_coordinates A h
  letI := hsep
  let f : E →ₐ[k] K := IsAlgClosed.lift
  letI : Algebra E K := f.toRingHom.toAlgebra
  letI : IsScalarTower k E K := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (f.commutes a).symm)
  let M := StandardLattice.{u} r
  let iE : extendedHopf K (groupAlgebra E M) ≅ groupAlgebra K M :=
    CommHopfAlgCat.isoMk (R := K) (LinearAlgebraicGroups.CharacterDescent.groupAlgebraBaseChange E K M)
  let c : groupAlgebra K M ≅ extendedHopf K B :=
    iE.symm ≪≫ (extendedHopfFunctor K).mapIso d ≪≫ extendedHopfTower (K := E) K B
  have ht : Specs.CharacterDescent.IsTorus (extendedHopf K B) := by
    let iK : extendedHopf K (groupAlgebra K M) ≅ groupAlgebra K M :=
      CommHopfAlgCat.isoMk (R := K) (LinearAlgebraicGroups.CharacterDescent.groupAlgebraBaseChange K K M)
    exact ⟨K, inferInstance, inferInstance, inferInstance, r,
      ⟨iK.symm ≪≫ (extendedHopfFunctor K).mapIso c⟩⟩
  have ht' := (GeometricRadicals.torusCoordinateComparison (extendedHopf K B)).mpr ht
  obtain ⟨F, _, _, _, s, ⟨t⟩⟩ := ht'
  let j := extendedGroupIso K B ≪≫ (groupBaseChange k K).mapIso e
  exact ⟨F, inferInstance, inferInstance, inferInstance, s,
    ⟨(groupBaseChange K F).mapIso j.symm ≪≫ t⟩⟩

open private trivial_of_subsingleton_sections
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals

private theorem centralizerReductive_of_radicalInclusion
    (inclusion : UnipotentRadicalInclusion.{u}) : CentralizerReductive.{u} := by
  intro k _ A hA T S _ hS hst hT
  letI := hA.1
  letI := hA.2.1
  letI : ConnectedSpace A.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.val.X.hom
  obtain ⟨C, hC, hCs, hCc, _⟩ := CocharacterDynamics.torusCentralizer A S hS
  let K := AlgebraicClosure k
  let A' := baseChangedAlgebraicGroup K A
  let C' := closedSubgroupAlgebraicGroup C
  let U := Specs.GeometricRadicals.geometricUnipotentRadical C'
  let R := Specs.GeometricRadicals.geometricUnipotentRadical A
  obtain ⟨hTcl, hTmax⟩ := hT
  obtain ⟨hCcl, hCbase⟩ :=
    LinearAlgebraicGroups.centralizerSchemeBaseChange k K S.inclusion C hC
  let T' := baseChangedSubgroup K T hTcl
  let Ck := baseChangedSubgroup K C hCcl
  have hScl : IsClosedImmersion ((groupBaseChange k K).map S.inclusion).hom.hom.left := by
    exact MorphismProperty.of_isPullback
      (baseChangeMapIsPullback K S.inclusion.hom.hom).flip S.isClosedImmersion
  let S' := baseChangedSubgroup K S hScl
  have hS' : IsTorus S'.group := torus_baseChange_algClosure (closedSubgroupAlgebraicGroup S) hS
  have hST : IsSubgroupOf S' T' := by
    obtain ⟨j, hj⟩ := hst
    refine ⟨(groupBaseChange k K).map j, ?_⟩
    change (groupBaseChange k K).map j ≫ (groupBaseChange k K).map T.inclusion =
      (groupBaseChange k K).map S.inclusion
    rw [← Functor.map_comp, hj]
  have hAs : Smooth A'.val.X.hom :=
    MorphismProperty.pullback_snd _ _ hA.1
  have hAc : ConnectedSpace A'.val.X.left :=
    pullback_of_geometrically hA.2.1.geometrically_connectedSpace K (fieldSpecMap k K)
  have hU := GeometricRadicals.geometricUnipotentRadicalLargest C'
  have hR := GeometricRadicals.geometricUnipotentRadicalLargest A
  obtain ⟨j, hj⟩ := inclusion A' hAs hAc T' S' hTmax hS' hST Ck hCbase U R hU hR
  obtain ⟨e⟩ := hA.2.2
  letI : Subsingleton (rationalSections R.group) := ⟨fun x y ↦
    (cancel_mono e.hom.hom.hom).mp (isTerminalTensorUnit.hom_ext _ _)⟩
  letI : Mono j.hom.hom := mono_over _ (factor_closed hj)
  letI : Subsingleton (rationalSections U.group) := ⟨fun x y ↦
    (cancel_mono j.hom.hom).mp (Subsingleton.elim (x ≫ j.hom.hom) (y ≫ j.hom.hom))⟩
  refine ⟨C, hC, hCs, hCc, ?_⟩
  let Uk := closedSubgroupAlgebraicGroup (G := baseChangedAlgebraicGroup K C') U
  haveI : Subsingleton (rationalSections Uk.val) := inferInstanceAs (Subsingleton (rationalSections U.group))
  exact trivial_of_subsingleton_sections Uk hU.1.1

open LinearAlgebraicGroups.DiagonalizableFixedLocus (CoordinateCoaction fixedIdeal)
open private weight_induction weight_mul weight_algebraMap reflectAction coordinateCoaction
  affine_fixed_criterion diagonalSource AlgSpecObj conjugationAction
  isFixedBy_conjugation_iff isFixedBy_comp_equivariant isFixedBy_of_comp_equivariant
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus
open WeightDecomposition (weightSpace)
open private weightProjection projection_of_mem
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.WeightDecomposition

/-- Over a square-zero thickening, the weight-zero part of a lift of a fixed
point is again a ring map. The lift agrees with the original on weight zero. -/
private theorem project_fixed_lift {M A R : Type u} [CommGroup M]
    [CommRing A] [Algebra k A] [CommRing R] [Algebra k R]
    (ρ : CoordinateCoaction (k := k) (M := M) (A := A))
    (I : Ideal R) (hI : I ^ 2 = ⊥) (g : A →ₐ[k] R)
    (hg : fixedIdeal ρ ≤ RingHom.ker ((Ideal.Quotient.mkₐ k I).comp g)) :
    ∃ g' : A →ₐ[k] R, (Ideal.Quotient.mkₐ k I).comp g' = (Ideal.Quotient.mkₐ k I).comp g ∧
      fixedIdeal ρ ≤ RingHom.ker g' ∧
      ∀ a ∈ weightSpace ρ.toRightComodule 1, g' a = g a := by
  classical
  let p := weightProjection ρ.toRightComodule 1
  let L := g.toLinearMap.comp p
  have proj {m : M} {a : A} (ha : a ∈ weightSpace ρ.toRightComodule m) :
      p a = if m = 1 then a else 0 := projection_of_mem ha 1
  have killed {m : M} {a : A} (hm : m ≠ 1) (ha : a ∈ weightSpace ρ.toRightComodule m) :
      g a ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (hg (Ideal.subset_span ⟨m, hm, ha⟩))
  have mulHomogeneous (m n : M) (a b : A) (ha : a ∈ weightSpace ρ.toRightComodule m)
      (hb : b ∈ weightSpace ρ.toRightComodule n) : L (a * b) = L a * L b := by
    change g (p (a * b)) = g (p a) * g (p b)
    rw [proj (weight_mul ρ ha hb), proj ha, proj hb]
    by_cases hm : m = 1
    · subst m
      by_cases hn : n = 1 <;> simp [hn]
    · by_cases hn : n = 1
      · subst n
        simp [hm]
      · have hz : g a * g b = 0 := by
          have h := Ideal.mul_mem_mul (killed hm ha) (killed hn hb)
          simpa [← pow_two, hI] using h
        by_cases he : m * n = 1 <;> simp [hm, hn, he, hz]
  have hmul (a b : A) : L (a * b) = L a * L b := by
    refine weight_induction ρ (fun a ↦ ∀ b, L (a * b) = L a * L b) ?_ (by simp) ?_ b
    · intro m a ha b
      refine weight_induction ρ (fun b ↦ L (a * b) = L a * L b) ?_ (by simp) ?_
      · exact fun n b hb ↦ mulHomogeneous m n a b ha hb
      · intro c d hc hd
        rw [mul_add, map_add, hc, hd, map_add, mul_add]
    · intro c d hc hd b
      rw [add_mul, map_add, hc, hd, map_add, add_mul]
  have hscalar (c : k) : L (algebraMap k A c) = algebraMap k R c := by
    change g (p (algebraMap k A c)) = _
    rw [proj (weight_algebraMap ρ c), ite_eq_left rfl, g.commutes]
  let g' : A →ₐ[k] R :=
    { toFun := L
      map_zero' := map_zero L
      map_add' := map_add L
      map_one' := by simpa using hscalar 1
      map_mul' := hmul
      commutes' := hscalar }
  refine ⟨g', AlgHom.ext (fun x ↦ ?_), ?_, fun a ha ↦ ?_⟩
  · change (Ideal.Quotient.mkₐ k I) (L x) = (Ideal.Quotient.mkₐ k I) (g x)
    refine weight_induction ρ (fun a ↦ (Ideal.Quotient.mkₐ k I) (L a) =
      (Ideal.Quotient.mkₐ k I) (g a)) ?_ (by simp) ?_
    · intro m a ha
      change (Ideal.Quotient.mkₐ k I) (g (p a)) = _
      by_cases hm : m = 1
      · rw [proj ha, ite_eq_left hm]
      · rw [proj ha, ite_eq_right hm, map_zero, map_zero]
        exact (Ideal.Quotient.eq_zero_iff_mem.mpr (killed hm ha)).symm
    · intro a b ha hb
      simp only [map_add, ha, hb]
  · rw [fixedIdeal, Ideal.span_le]
    rintro a ⟨m, hm, ha⟩
    change g (p a) = 0
    simp [proj ha, hm]
  · change g (p a) = g a
    rw [proj ha, ite_eq_left rfl]


open CategoryTheory.Functor (OplaxMonoidal)
open scoped TensorProduct

open private smooth_of_lifts quotient from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterOpenCell
open private restrictAction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus

local instance (K : Type u) [Field K] : (testSpec K).Braided :=
  AlgebraicGeometry.braidedAlgSpec (R := CommRingCat.of K)

local instance {M : Type u} [CommGroup M] :
    MonObj (AlgSpecObj k (MonoidAlgebra k M)) :=
  Functor.monObjObj (F := testSpec k) (diagonalSource (k := k) (M := M))
open private isFixedBy_groupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.FixedPointSchemes
open private split_of_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private centralizes_precomp_iso centralizes_iff_affine
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer

/-- Taking the fixed scheme preserves smoothness over an affine base with
trivial action. The projection onto weight zero preserves the base functions. -/
private theorem affine_fixed_relative_smooth {M A D : Type u} [CommGroup M]
    [CommRing A] [Algebra k A] [CommRing D] [Algebra k D]
    (a : ModObj (AlgSpecObj k (MonoidAlgebra k M)) (AlgSpecObj k A))
    (f : D →ₐ[k] A) {W : SchemeOver k}
    (r : W ⟶ AlgSpecObj k A) [Mono r]
    (hr : RepresentsFixedPoints a.smul r) (haW : IsAffine W.left)
    (hfW : LocallyOfFiniteType W.hom) (hfD : LocallyOfFiniteType (AlgSpecObj k D).hom)
    (hp : Smooth ((testSpec k).map (CommAlgCat.ofHom f).op).left)
    (hinv : a.smul ≫ (testSpec k).map (CommAlgCat.ofHom f).op =
      snd _ _ ≫ (testSpec k).map (CommAlgCat.ofHom f).op) :
    Smooth (r ≫ (testSpec k).map (CommAlgCat.ofHom f).op).left := by
  let F := testSpec k
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let : F.Braided := AlgebraicGeometry.braidedAlgSpec (R := CommRingCat.of k)
  let H := diagonalSource (k := k) (M := M)
  let X := op (CommAlgCat.of k A)
  let a' := reflectAction F ff H X a
  let ρ := coordinateCoaction a'
  have hbase (d : D) : f d ∈ weightSpace ρ.toRightComodule 1 := by
    have h : a'.smul ≫ (CommAlgCat.ofHom f).op =
        snd H X ≫ (CommAlgCat.ofHom f).op := by
      apply ff.map_injective
      have hfst := CartesianMonoidalCategory.prodComparison_snd F H X
      rw [← OplaxMonoidal.δ_of_cartesianMonoidalCategory] at hfst
      change F.map (a'.smul ≫ _) = F.map (snd H X ≫ _)
      have ha' : F.map a'.smul = OplaxMonoidal.δ F H X ≫ a.smul := by
        change F.map (ff.preimage (OplaxMonoidal.δ F H X ≫ a.smul)) = _
        exact ff.map_preimage _
      rw [F.map_comp, F.map_comp, ha', Category.assoc, hinv, ← Category.assoc, hfst]
    have hd := congrArg (fun g ↦ g.unop.hom d) h
    change a'.smul.unop.hom (f d) = (1 : MonoidAlgebra k M) ⊗ₜ[k] f d at hd
    rw [WeightDecomposition.mem_weightSpace, ρ.coaction_eq]
    change TensorProduct.comm k (MonoidAlgebra k M) A (a'.smul.unop.hom (f d)) =
      f d ⊗ₜ[k] MonoidAlgebra.of k M 1
    rw [hd, TensorProduct.comm_tmul, map_one]
  change Smooth (Spec.map (CommRingCat.ofHom f.toRingHom)) at hp
  have hsm := (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hp
  let : Algebra D A := f.toRingHom.toAlgebra
  have hfs : Algebra.FormallySmooth D A := hsm.formallySmooth
  apply smooth_of_lifts haW (inferInstanceAs (IsAffine (Spec (.of D)))) hfW hfD
  intro R _ _ I hI x y hxy
  let x₀ : A →ₐ[k] (R ⧸ I) := (ff.preimage (x ≫ r)).unop.hom
  let y₀ : D →ₐ[k] R := (ff.preimage y).unop.hom
  have hx₀ : F.map (CommAlgCat.ofHom x₀).op = x ≫ r := ff.map_preimage _
  have hy₀ : F.map (CommAlgCat.ofHom y₀).op = y := ff.map_preimage _
  have heq : x₀.comp f = (Ideal.Quotient.mkₐ k I).comp y₀ := by
    have h : (CommAlgCat.ofHom (x₀.comp f)).op =
        (CommAlgCat.ofHom ((Ideal.Quotient.mkₐ k I).comp y₀)).op := by
      apply ff.map_injective
      change F.map ((CommAlgCat.ofHom x₀).op ≫ (CommAlgCat.ofHom f).op) =
        F.map ((quotient I).op ≫ (CommAlgCat.ofHom y₀).op)
      simpa only [F.map_comp, hx₀, hy₀, Category.assoc, mapPoints] using hxy
    exact congrArg (fun g ↦ g.unop.hom) h
  let : Algebra D R := y₀.toRingHom.toAlgebra
  let xD : A →ₐ[D] (R ⧸ I) :=
    { toRingHom := x₀.toRingHom
      commutes' := fun d ↦ DFunLike.congr_fun heq d }
  obtain ⟨gD, hgD⟩ := (Algebra.FormallySmooth.iff_comp_surjective.mp hfs) I hI xD
  let g : A →ₐ[k] R :=
    { toRingHom := gD.toRingHom
      commutes' := fun c ↦ by
        rw [← f.commutes c]
        exact (gD.commutes (algebraMap k D c)).trans (y₀.commutes c) }
  have hg : (Ideal.Quotient.mkₐ k I).comp g = x₀ :=
    AlgHom.ext (fun a ↦ DFunLike.congr_fun hgD a)
  have hxfix := (hr _ (x ≫ r)).mpr ⟨x, rfl⟩
  rw [← hx₀] at hxfix
  have hxker : fixedIdeal ρ ≤ RingHom.ker x₀ :=
    (affine_fixed_criterion (M := M) a x₀).mp hxfix
  obtain ⟨g', hg', hker, hzero⟩ := project_fixed_lift ρ I hI g (hg.symm ▸ hxker)
  have hpoint := (affine_fixed_criterion (M := M) a g').mpr hker
  obtain ⟨x', hx'⟩ := (hr _ _).mp hpoint
  refine ⟨x', ?_, ?_⟩
  · apply (cancel_mono r).mp
    rw [mapPoints, Category.assoc, hx', ← F.map_comp]
    change F.map (CommAlgCat.ofHom ((Ideal.Quotient.mkₐ k I).comp g')).op = x ≫ r
    rw [hg', hg, hx₀]
  · rw [← Category.assoc, hx', ← F.map_comp]
    have h : g'.comp f = y₀ :=
      AlgHom.ext (fun d ↦ (hzero _ (hbase d)).trans (gD.commutes d))
    change F.map (CommAlgCat.ofHom (g'.comp f)).op = y
    rw [h, hy₀]

private theorem fixed_relative_smooth {M : Type u} [CommGroup M]
    {V W U : SchemeOver k}
    (a : ModObj (AlgSpecObj k (MonoidAlgebra k M)) V)
    (r : W ⟶ V) [Mono r] (p : V ⟶ U)
    (hV : IsAffine V.left) (hW : IsAffine W.left) (hU : IsAffine U.left)
    (hfW : LocallyOfFiniteType W.hom) (hfU : LocallyOfFiniteType U.hom)
    (hp : Smooth p.left) (hr : RepresentsFixedPoints a.smul r)
    (hinv : a.smul ≫ p = snd _ _ ≫ p) : Smooth (r ≫ p).left := by
  obtain ⟨A, ⟨eV⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hV
  obtain ⟨D, ⟨eU⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hU
  let F := testSpec k
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let H := AlgSpecObj k (MonoidAlgebra k M)
  letI : ModObj H V := a
  letI : IsMonHom (Iso.refl H).hom := by change IsMonHom (𝟙 H); infer_instance
  let a' := ModObj.ofIso (Iso.refl H) eV.symm
  let p' := eV.hom ≫ p ≫ eU.inv
  let r' := r ≫ eV.inv
  let f := (ff.preimage p').unop.hom
  have hf : F.map (CommAlgCat.ofHom f).op = p' := ff.map_preimage _
  have ha : a'.smul ≫ eV.hom = (H ◁ eV.hom) ≫ a.smul := by
    change ((𝟙 H ⊗ₘ eV.hom) ≫ a.smul ≫ eV.inv) ≫ eV.hom = _
    simp [whiskerLeft]
  have hinv' : a'.smul ≫ F.map (CommAlgCat.ofHom f).op =
      snd H (F.obj A) ≫ F.map (CommAlgCat.ofHom f).op := by
    rw [hf]
    change a'.smul ≫ eV.hom ≫ p ≫ eU.inv = snd H (F.obj A) ≫ eV.hom ≫ p ≫ eU.inv
    rw [reassoc_of% ha, reassoc_of% hinv, whiskerLeft_snd_assoc]
  have hr' : RepresentsFixedPoints a'.smul r' := by
    intro T t
    have he : IsFixedBy a'.smul t ↔ IsFixedBy a.smul (t ≫ eV.hom) := by
      refine ⟨isFixedBy_comp_equivariant ha, ?_⟩
      intro ht
      unfold IsFixedBy at ht ⊢
      apply (cancel_mono eV.hom).mp
      simpa only [Category.assoc, ha, whiskerLeft_comp] using ht
    rw [he, hr]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change y ≫ r ≫ eV.inv = t
      exact (eV.comp_inv_eq).mpr hy
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change y ≫ r ≫ eV.inv = t at hy
      exact (eV.comp_inv_eq).mp hy
  haveI : IsIso eV.hom.left := (Over.forget _).map_isIso _
  haveI : IsIso eU.inv.left := (Over.forget _).map_isIso _
  haveI : IsIso eU.hom.left := (Over.forget _).map_isIso _
  haveI : Mono r' := inferInstanceAs (Mono (r ≫ eV.inv))
  letI := hp
  letI := hfU
  have hp' : Smooth (F.map (CommAlgCat.ofHom f).op).left := by
    rw [hf]
    change Smooth (eV.hom.left ≫ p.left ≫ eU.inv.left)
    infer_instance
  have hfD : LocallyOfFiniteType (F.obj D).hom := by rw [← Over.w eU.hom]; infer_instance
  have h := affine_fixed_relative_smooth (M := M) a' f r' hr' hW hfW hfD hp' hinv'
  rw [hf, show r' ≫ p' = r ≫ p ≫ eU.inv by simp [r', p']] at h
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @Smooth)
    (r.left ≫ p.left) eU.inv.left).mp (by simpa only [Over.comp_left, Category.assoc] using h)

open private orbitMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SmoothOrbit
open private projection_eq_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.QuotientEmbedding
open private quotientSmooth compareRepresentatives compareRepresentatives_projection
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient

private abbrev restrictGroupAction {H : GroupScheme k} {X : SchemeOver k}
    (d : H ⟶ G) (a : ModObj G.X X) : ModObj H.X X :=
  letI := a
  Mod.scalarRestriction d.hom.hom X

private theorem restrictGroupAction_on_points {H : GroupScheme k} {X T : SchemeOver k}
    (d : H ⟶ G) (a : ModObj G.X X) (h : T ⟶ H.X) (x : T ⟶ X) :
    lift h x ≫ (restrictGroupAction d a).smul = lift (h ≫ d.hom.hom) x ≫ a.smul := by
  change lift h x ≫ (d.hom.hom ▷ X) ≫ a.smul = _
  rw [← Category.assoc, lift_whiskerRight]

private theorem fixed_iff_families {H X T : SchemeOver k} (a : H ⊗ X ⟶ X)
    (x : T ⟶ X) :
    IsFixedBy a x ↔ ∀ (Y : SchemeOver k) (h : Y ⟶ H) (y : Y ⟶ T),
      lift h (y ≫ x) ≫ a = y ≫ x := by
  unfold IsFixedBy
  constructor
  · intro e Y h y
    simpa only [← Category.assoc, lift_whiskerLeft, lift_snd] using
      congrArg (fun f ↦ lift h y ≫ f) e
  · intro e
    simpa only [← lift_whiskerLeft_assoc, lift_fst_snd, Category.id_comp] using
      e (H ⊗ T) (fst H T) (snd H T)

private theorem centralizer_commutes {S C : ClosedSubgroup G}
    (hC : IsCentralizer S C) {Y : SchemeOver k} (s : Y ⟶ S.group.X) (c : Y ⟶ C.group.X) :
    Commute (c ≫ C.inclusion.hom.hom) (s ≫ S.inclusion.hom.hom) := by
  have h := (hC _ _).mpr ⟨c, rfl⟩
  unfold Centralizes conjugateFamily at h
  have hh := congrArg (fun f ↦ lift s (𝟙 Y) ≫ f) h
  simp only [MonObj.comp_mul, GrpObj.comp_inv, lift_snd_assoc, lift_fst_assoc,
    Category.id_comp] at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

private theorem centralizer_action {S C : ClosedSubgroup G} (hC : IsCentralizer S C)
    {X Z : SchemeOver k} (a : ModObj G.X X) (i : Z ⟶ X)
    (hi : IsClosedImmersion i.left) (hrep : RepresentsFixedPoints
      (restrictGroupAction S.inclusion a).smul i) :
    ∃ b : ModObj C.group.X Z, b.smul ≫ i = (C.inclusion.hom.hom ⊗ₘ i) ≫ a.smul := by
  letI := a
  let aC := restrictGroupAction C.inclusion a
  let f := (C.group.X ◁ i) ≫ aC.smul
  have hf : f = (C.inclusion.hom.hom ⊗ₘ i) ≫ a.smul := by
    change (_ ◁ i) ≫ (C.inclusion.hom.hom ▷ X) ≫ a.smul = _
    rw [← Category.assoc, ← tensorHom_def']
  have hfixed : IsFixedBy (restrictGroupAction S.inclusion a).smul f := by
    apply (fixed_iff_families _ _).mpr
    intro Y s y
    let c := y ≫ fst C.group.X Z
    let v := (y ≫ snd C.group.X Z) ≫ i
    have hv : (s ≫ S.inclusion.hom.hom) • v = v := by
      have hi' := (hrep _ i).mpr ⟨𝟙 _, Category.id_comp _⟩
      have hh := (fixed_iff_families _ _).mp hi' Y s (y ≫ snd C.group.X Z)
      simpa only [restrictGroupAction_on_points, CategoryTheory.Hom.smul_def, v] using hh
    have hy : y ≫ f = (c ≫ C.inclusion.hom.hom) • v := by
      rw [hf]
      simp only [CategoryTheory.Hom.smul_def, c, v, Category.assoc]
      rw [← Category.assoc]
      congr 1
      apply CartesianMonoidalCategory.hom_ext <;> simp
    change (lift s (y ≫ f) ≫ (S.inclusion.hom.hom ▷ X)) ≫ a.smul = _
    rw [lift_whiskerRight, ← CategoryTheory.Hom.smul_def, hy, ← mul_smul,
      ← (centralizer_commutes hC s c).eq, mul_smul, hv]
  obtain ⟨b, hb⟩ := (hrep _ f).mp hfixed
  letI : Mono i := mono_over i hi
  exact ⟨restrictAction aC i b hb, hb.trans hf⟩

private theorem orbit_conjugation_equivariant {H : GroupScheme k} {X : SchemeOver k}
    (d : H ⟶ G) (a : ModObj G.X X) (x : 𝟙_ (SchemeOver k) ⟶ X)
    (hx : IsFixedBy (restrictGroupAction d a).smul x) :
    (conjugationAction d).smul ≫ Specs.SmoothOrbit.orbitMap a x =
      (H.X ◁ Specs.SmoothOrbit.orbitMap a x) ≫ (restrictGroupAction d a).smul := by
  letI := a
  let X' := H.X ⊗ G.X
  let h := fst H.X G.X ≫ d.hom.hom
  let g := snd H.X G.X
  let x' := toUnit X' ≫ x
  have hh : h • x' = x' := by
    have e := (fixed_iff_families _ _).mp hx X' (fst _ _) (toUnit _)
    simpa only [restrictGroupAction_on_points, CategoryTheory.Hom.smul_def, h, x'] using e
  have hi : h⁻¹ • x' = x' :=
    calc h⁻¹ • x' = h⁻¹ • (h • x') := congrArg (h⁻¹ • ·) hh.symm
      _ = x' := inv_smul_smul h x'
  have hc : (conjugationAction d).smul = h * g * h⁻¹ := by
    change (d.hom.hom ▷ G.X) ≫ GrpObj.conj G.X = _
    simp [GrpObj.conj, MonObj.comp_mul, GrpObj.comp_inv, h, g]
  have hf : (H.X ◁ Specs.SmoothOrbit.orbitMap a x) ≫ (restrictGroupAction d a).smul =
      h • (g ≫ Specs.SmoothOrbit.orbitMap a x) := by
    rw [show H.X ◁ Specs.SmoothOrbit.orbitMap a x =
      lift (fst H.X G.X) (g ≫ Specs.SmoothOrbit.orbitMap a x) by
        apply CartesianMonoidalCategory.hom_ext <;> simp [g]]
    change (lift _ _ ≫ (d.hom.hom ▷ X)) ≫ a.smul = _
    rw [lift_whiskerRight]
    rfl
  rw [hc, hf, orbitMap_comp, orbitMap_comp, mul_smul, mul_smul]
  change h • (g • (h⁻¹ • x')) = h • (g • x')
  rw [hi]

/-- A smooth equivariant map with affine source induces a smooth map
between the two fixed schemes. Work over affine opens of the fixed target. -/
private theorem smooth_map_on_fixed_schemes {M : Type u} [CommGroup M]
    {X Y C Z : SchemeOver k}
    (a : ModObj (AlgSpecObj k (MonoidAlgebra k M)) X)
    (b : ModObj (AlgSpecObj k (MonoidAlgebra k M)) Y)
    (f : X ⟶ Y) (q : C ⟶ Z) (i : C ⟶ X) (j : Z ⟶ Y)
    (hi : IsClosedImmersion i.left) (hj : IsClosedImmersion j.left)
    (hX : IsAffine X.left) (hC : LocallyOfFiniteType C.hom) (hY : IsSeparated Y.hom)
    (hZ : LocallyOfFiniteType Z.hom) (hs : Smooth f.left)
    (he : a.smul ≫ f = (_ ◁ f) ≫ b.smul)
    (hq : q ≫ j = i ≫ f)
    (hrC : RepresentsFixedPoints a.smul i) (hrZ : RepresentsFixedPoints b.smul j) :
    Smooth q.left := by
  let H := AlgSpecObj k (MonoidAlgebra k M)
  haveI : IsClosedImmersion i.left := hi
  haveI : IsClosedImmersion j.left := hj
  haveI : IsAffine X.left := hX
  haveI : IsAffine C.left := isAffine_of_isAffineHom i.left
  haveI : IsSeparated Y.hom := hY
  haveI : IsSeparated Z.hom := by rw [← Over.w j]; infer_instance
  haveI : IsAffineHom (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  haveI : IsAffineHom (q.left ≫ Z.hom) := by rw [Over.w q]; infer_instance
  haveI : IsAffineHom f.left := IsAffineHom.of_comp f.left Y.hom
  haveI : IsAffineHom q.left := IsAffineHom.of_comp q.left Z.hom
  haveI : Mono i := Over.mono_of_mono_left _
  haveI : Mono j := Over.mono_of_mono_left _
  let Ucov := Z.left.affineCover
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := @Smooth) Ucov).mpr
  intro s
  let U : SchemeOver k := Over.mk (Ucov.f s ≫ Z.hom)
  let u : U ⟶ Z := Over.homMk (Ucov.f s) rfl
  let W := pullback q u
  let V := pullback f (u ≫ j)
  let w : W ⟶ C := pullback.fst q u
  let pW : W ⟶ U := pullback.snd q u
  let v : V ⟶ X := pullback.fst f (u ≫ j)
  let p : V ⟶ U := pullback.snd f (u ≫ j)
  have hv : v ≫ f = p ≫ u ≫ j := pullback.condition
  have hw : w ≫ q = pW ≫ u := pullback.condition
  haveI : IsOpenImmersion u.left := inferInstanceAs (IsOpenImmersion (Ucov.f s))
  haveI : Mono u := Over.mono_of_mono_left _
  haveI : Mono v := inferInstanceAs (Mono (pullback.fst f (u ≫ j)))
  have sqV : IsPullback v.left p.left f.left (u ≫ j).left :=
    (IsPullback.of_hasPullback f (u ≫ j)).map (Over.forget _)
  have sqW : IsPullback w.left pW.left q.left u.left :=
    (IsPullback.of_hasPullback q u).map (Over.forget _)
  haveI : IsAffine U.left := inferInstanceAs (IsAffine (Ucov.X s))
  haveI : IsAffine V.left := IsAffine.of_isPullback sqV.flip
  haveI : IsAffine W.left := IsAffine.of_isPullback sqW.flip
  haveI : IsOpenImmersion w.left := MorphismProperty.of_isPullback sqW.flip
    (show IsOpenImmersion u.left from inferInstance)
  haveI : LocallyOfFiniteType C.hom := hC
  haveI : LocallyOfFiniteType Z.hom := hZ
  have hW : LocallyOfFiniteType W.hom := by rw [← Over.w w]; infer_instance
  have hU : LocallyOfFiniteType U.hom := by rw [← Over.w u]; infer_instance
  have hp : Smooth p.left := MorphismProperty.of_isPullback sqV hs
  have ht : IsFixedBy b.smul (u ≫ j) := (hrZ _ _).mpr ⟨u, rfl⟩
  have hAct : ((H ◁ v) ≫ a.smul) ≫ f = (snd H V ≫ p) ≫ (u ≫ j) := by
    rw [Category.assoc, he, ← whiskerLeft_comp_assoc, hv, whiskerLeft_comp, Category.assoc,
      ht, whiskerLeft_snd_assoc, Category.assoc]
  let sm := pullback.lift ((H ◁ v) ≫ a.smul) (snd H V ≫ p) hAct
  have hsmv : sm ≫ v = (H ◁ v) ≫ a.smul := pullback.lift_fst _ _ _
  have hsmp : sm ≫ p = snd H V ≫ p := pullback.lift_snd _ _ _
  let aV := restrictAction a v sm hsmv
  have hwi : (w ≫ i) ≫ f = pW ≫ (u ≫ j) := by
    rw [Category.assoc, ← hq, ← Category.assoc, hw, Category.assoc]
  let r : W ⟶ V := pullback.lift (w ≫ i) pW hwi
  have hrv : r ≫ v = w ≫ i := pullback.lift_fst _ _ _
  have hrp : r ≫ p = pW := pullback.lift_snd _ _ _
  haveI : Mono w := inferInstanceAs (Mono (pullback.fst q u))
  haveI : Mono (r ≫ v) := hrv.symm ▸ inferInstanceAs (Mono (w ≫ i))
  haveI : Mono r := mono_of_mono r v
  have hr : RepresentsFixedPoints aV.smul r := by
    intro T x
    have hfix : IsFixedBy aV.smul x ↔ IsFixedBy a.smul (x ≫ v) := by
      exact ⟨isFixedBy_comp_equivariant hsmv, isFixedBy_of_comp_equivariant hsmv⟩
    rw [hfix, hrC]
    constructor
    · rintro ⟨c, hc⟩
      have hcu : c ≫ q = (x ≫ p) ≫ u := by
        apply (cancel_mono j).mp
        rw [Category.assoc, hq, ← Category.assoc, hc, Category.assoc, hv,
          Category.assoc, Category.assoc]
      refine ⟨pullback.lift c (x ≫ p) hcu, (cancel_mono v).mp ?_⟩
      rw [Category.assoc, hrv, pullback.lift_fst_assoc, hc]
    · rintro ⟨t, ht⟩
      exact ⟨t ≫ w, by rw [Category.assoc, ← hrv, ← Category.assoc, ht]⟩
  have h := fixed_relative_smooth (M := M) aV r p inferInstance inferInstance inferInstance
    hW hU hp hr hsmp
  rw [hrp] at h
  change Smooth (pullback.snd q.left u.left)
  apply (MorphismProperty.cancel_left_of_respectsIso (P := @Smooth) sqW.isoPullback.hom _).mp
  rw [sqW.isoPullback_hom_snd]
  exact h

private abbrev translationMap {Z : SchemeOver k} (a : ModObj G.X Z)
    (g : 𝟙_ (SchemeOver k) ⟶ G.X) : Z ⟶ Z :=
  lift (toUnit Z ≫ g) (𝟙 Z) ≫ a.smul

private theorem comp_translationMap {Z T : SchemeOver k} (a : ModObj G.X Z)
    (g : 𝟙_ (SchemeOver k) ⟶ G.X) (z : T ⟶ Z) :
    letI := a
    z ≫ translationMap a g = (toUnit T ≫ g) • z := by
  letI := a
  simp only [translationMap, CategoryTheory.Hom.smul_def, comp_lift_assoc, comp_toUnit_assoc,
    Category.comp_id]

private def translationIso {Z : SchemeOver k} (a : ModObj G.X Z)
    (g : 𝟙_ (SchemeOver k) ⟶ G.X) : Z ≅ Z := by
  letI := a
  have hm (g h : 𝟙_ (SchemeOver k) ⟶ G.X) :
      translationMap a g ≫ translationMap a h = translationMap a (h * g) := by
    rw [comp_translationMap]
    change (toUnit Z ≫ h) • (toUnit Z ≫ g) • (𝟙 Z) = (toUnit Z ≫ (h * g)) • (𝟙 Z)
    rw [← mul_smul, MonObj.comp_mul]
  have ho : translationMap a (1 : 𝟙_ (SchemeOver k) ⟶ G.X) = 𝟙 Z := by
    change (toUnit Z ≫ (1 : 𝟙_ (SchemeOver k) ⟶ G.X)) • (𝟙 Z) = 𝟙 Z
    rw [MonObj.comp_one, one_smul]
  exact ⟨translationMap a g, translationMap a g⁻¹, by rw [hm, inv_mul_cancel, ho],
    by rw [hm, mul_inv_cancel, ho]⟩

private theorem orbitMap_translate {Z : SchemeOver k} (a : ModObj G.X Z)
    (z y : 𝟙_ (SchemeOver k) ⟶ Z) (g : 𝟙_ (SchemeOver k) ⟶ G.X)
    (hg : g ≫ Specs.SmoothOrbit.orbitMap a z = y) :
    Specs.SmoothOrbit.orbitMap a y = (rightTranslation g).hom ≫
      Specs.SmoothOrbit.orbitMap a z := by
  letI := a
  rw [← hg]
  change (𝟙 G.X) • (toUnit G.X ≫ g ≫ Specs.SmoothOrbit.orbitMap a z) =
    ((𝟙 G.X) * (toUnit G.X ≫ g)) ≫ Specs.SmoothOrbit.orbitMap a z
  rw [← Category.assoc, orbitMap_comp, orbitMap_comp, mul_smul]

private theorem translation_at_point {Z : SchemeOver k} (a : ModObj G.X Z)
    (z : 𝟙_ (SchemeOver k) ⟶ Z) (g : 𝟙_ (SchemeOver k) ⟶ G.X) :
    z ≫ (translationIso a g).hom = g ≫ Specs.SmoothOrbit.orbitMap a z := by
  change z ≫ translationMap a g = _
  rw [comp_translationMap, orbitMap_comp, toUnit_unique (toUnit _) (𝟙 _),
    Category.id_comp, Category.id_comp]

private theorem point_in_orbit {Z : SchemeOver k} (a : ModObj G.X Z)
    (z : 𝟙_ (SchemeOver k) ⟶ Z) :
    z.left (IsLocalRing.closedPoint k) ∈ Specs.SmoothOrbit.orbitSet a z := by
  refine ⟨η[G.X].left (IsLocalRing.closedPoint k), ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left]
  have h : (1 : 𝟙_ (SchemeOver k) ⟶ G.X) ≫ Specs.SmoothOrbit.orbitMap a z = z := by
    rw [orbitMap_comp, one_smul, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  exact congrArg (fun f : 𝟙_ (SchemeOver k) ⟶ Z ↦ f.left (IsLocalRing.closedPoint k)) h

private def rationalPointOfClosed [IsAlgClosed k] {Z : SchemeOver k}
    [LocallyOfFiniteType Z.hom] (z : Z.left) (hz : IsClosed {z}) : 𝟙_ (SchemeOver k) ⟶ Z :=
  Over.homMk (pointOfClosedPoint Z.hom z hz) (pointOfClosedPoint_comp Z.hom z hz)

private theorem rationalPointOfClosed_apply [IsAlgClosed k] {Z : SchemeOver k}
    [LocallyOfFiniteType Z.hom] (z : Z.left) (hz : IsClosed {z}) :
    (rationalPointOfClosed z hz).left (IsLocalRing.closedPoint k) = z :=
  pointOfClosedPoint_apply _ _ _ _

private theorem all_of_open_contains_closed {Z : Scheme.{u}} [JacobsonSpace Z] {U : Set Z}
    (hU : IsOpen U) (h : ∀ z : Z, IsClosed {z} → z ∈ U) (z : Z) : z ∈ U := by
  by_contra hz
  obtain ⟨w, hw, hw'⟩ := nonempty_inter_closedPoints (show Uᶜ.Nonempty from ⟨z, hz⟩)
    hU.isClosed_compl.isLocallyClosed
  exact hw (h w hw')

private theorem reduced_of_flat_local_cover {Z X : Scheme.{u}} [IsReduced X]
    (q : ∀ z : Z, ∃ (f : X ⟶ Z) (_ : Flat f) (x : X), f x = z) : IsReduced Z := by
  haveI (z : Z) : _root_.IsReduced (Z.presheaf.stalk z) := by
    obtain ⟨f, hf, x, rfl⟩ := q z
    letI := hf
    algebraize [(f.stalkMap x).hom]
    haveI : Module.FaithfullyFlat (Z.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap f x) (f.toLRSHom.prop x)
    exact isReduced_of_injective (f.stalkMap x).hom
      (FaithfulSMul.algebraMap_injective (Z.presheaf.stalk (f x)) (X.presheaf.stalk x))
  exact isReduced_of_isReduced_stalk Z

private theorem proper_orbits_of_smooth_maps [IsAlgClosed k] (A : AffineAlgebraicGroup k)
    {Z : SchemeOver k} (a : ModObj A.val.X Z)
    (hA : Smooth A.val.X.hom) (hZ : IsProper Z.hom)
    (hs : ∀ z : 𝟙_ (SchemeOver k) ⟶ Z, Smooth (Specs.SmoothOrbit.orbitMap a z).left) :
    Smooth Z.hom ∧ ∀ z : 𝟙_ (SchemeOver k) ⟶ Z, Nonempty (ProperOrbit a z) := by
  let f := Specs.SmoothOrbit.orbitMap a
  let V := Specs.SmoothOrbit.orbitSet a
  letI := hZ
  letI : JacobsonSpace Z.left := LocallyOfFiniteType.jacobsonSpace Z.hom
  have ho z : IsOpen (V z) := by
    letI := hs z
    simpa only [V, Specs.SmoothOrbit.orbitSet, Set.image_univ] using
      (f z).left.isOpenMap _ isOpen_univ
  have hall (t : Z.left) : ∃ z, t ∈ V z := by
    have ht : t ∈ ⋃ z, V z := all_of_open_contains_closed (isOpen_iUnion ho) (fun y hy ↦ by
      let z := rationalPointOfClosed y hy
      exact Set.mem_iUnion.mpr ⟨z, rationalPointOfClosed_apply y hy ▸ point_in_orbit a z⟩) t
    exact Set.mem_iUnion.mp ht
  have htrans (y z : 𝟙_ (SchemeOver k) ⟶ Z)
      (hy : y.left (IsLocalRing.closedPoint k) ∈ V z) : V y = V z := by
    obtain ⟨g, hg⟩ := (SmoothOrbit.geometricOrbitLifts k A Z a z y).mp hy
    change Set.range (Specs.SmoothOrbit.orbitMap a y).left =
      Set.range (Specs.SmoothOrbit.orbitMap a z).left
    rw [orbitMap_translate a z y g hg, Over.comp_left]
    haveI : IsIso (rightTranslation g).hom.left :=
      (Over.forget _).map_isIso (rightTranslation g).hom
    exact (congrArg Set.range (funext (Scheme.Hom.comp_apply _ _))).trans
      ((rightTranslation g).hom.left.surjective.range_comp _)
  have heq (x y : 𝟙_ (SchemeOver k) ⟶ Z) (hxy : (V x ∩ V y).Nonempty) : V x = V y := by
    obtain ⟨p, hp, hpC⟩ := nonempty_inter_closedPoints hxy ((ho x).inter (ho y)).isLocallyClosed
    let z := rationalPointOfClosed p hpC
    have hx : V z = V x := htrans z x (rationalPointOfClosed_apply p hpC ▸ hp.1)
    have hy : V z = V y := htrans z y (rationalPointOfClosed_apply p hpC ▸ hp.2)
    exact hx.symm.trans hy
  have hc z : IsClosed (V z) := by
    rw [← isOpen_compl_iff]
    have h : (V z)ᶜ = ⋃ y : {y // ¬ (V z ∩ V y).Nonempty}, V y.val := by
      ext t
      constructor
      · intro ht
        obtain ⟨y, hy⟩ := hall t
        exact Set.mem_iUnion.mpr ⟨⟨y, fun h ↦ ht (heq z y h ▸ hy)⟩, hy⟩
      · intro ht htz
        obtain ⟨y, hy⟩ := Set.mem_iUnion.mp ht
        exact y.property ⟨t, htz, hy⟩
    rw [h]
    exact isOpen_iUnion (fun y ↦ ho y.val)
  letI := hA
  haveI : IsReduced A.val.X.left := isReduced_of_smooth_over_field A.val.X.hom
  haveI : IsReduced Z.left := reduced_of_flat_local_cover (fun t ↦ by
    obtain ⟨z, x, hx⟩ := hall t
    letI := hs z
    exact ⟨(f z).left, inferInstance, x, hx⟩)
  have hd := Scheme.Hom.dense_smoothLocus_of_perfectField Z.hom
  have hz (z : 𝟙_ (SchemeOver k) ⟶ Z) :
      z.left (IsLocalRing.closedPoint k) ∈ Z.hom.smoothLocus := by
    have h := hd.inter_open_nonempty (V z) (ho z) ⟨_, point_in_orbit a z⟩
    obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints h
      ((ho z).inter Z.hom.smoothLocus.isOpen).isLocallyClosed
    let y := rationalPointOfClosed x hxc
    obtain ⟨g, hg⟩ := (SmoothOrbit.geometricOrbitLifts k A Z a z y).mp
      (rationalPointOfClosed_apply x hxc ▸ hx.1)
    let e := translationIso a g
    haveI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
    have hpre : e.hom.left ⁻¹ᵁ Z.hom.smoothLocus = Z.hom.smoothLocus := by
      simp only [Scheme.Hom.preimage_smoothLocus_eq, Over.w e.hom]
    have hxy : e.hom.left (z.left (IsLocalRing.closedPoint k)) = x := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, translation_at_point, hg,
        rationalPointOfClosed_apply]
    rw [← hpre, Scheme.Hom.mem_preimage, hxy]
    exact hx.2
  have hSm : Smooth Z.hom := by
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    apply top_unique
    intro x _
    apply all_of_open_contains_closed Z.hom.smoothLocus.isOpen _ x
    intro y hy
    exact rationalPointOfClosed_apply y hy ▸ hz (rationalPointOfClosed y hy)
  refine ⟨hSm, fun z ↦ ?_⟩
  let U : Z.left.Opens := ⟨V z, ho z⟩
  let O : SchemeOver k := Over.mk (U.ι ≫ Z.hom)
  let i : O ⟶ Z := Over.homMk U.ι rfl
  haveI : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion U.ι)
  have hι : Set.range i.left = V z := Scheme.Opens.range_ι U
  have hfac : Set.range (f z).left ⊆ Set.range i.left := hι.ge
  let p := IsOpenImmersion.lift i.left (f z).left hfac
  have hp : p ≫ i.left = (f z).left := IsOpenImmersion.lift_fac _ _ _
  let q : A.val.X ⟶ O := Over.homMk p (by
    change p ≫ i.left ≫ Z.hom = _
    rw [← Category.assoc, hp, Over.w])
  haveI : IsClosedImmersion i.left := IsClosedImmersion.of_isPreimmersion _ (hι.symm ▸ hc z)
  have hq : Smooth q.left := MorphismProperty.of_isPullback
    (IsOpenImmersion.isPullback_lift_id (f z).left i.left hfac).flip (hs z)
  have hsurj : Surjective q.left := ⟨fun y ↦ by
    have hy : i.left y ∈ V z := hι ▸ Set.mem_range_self y
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, i.left.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply]
    change (p ≫ i.left) x = i.left y
    rw [hp]
    exact hx⟩
  exact ⟨⟨O, i, q, Over.OverMorphism.ext hp, inferInstance, inferInstance, hq, hsurj,
    inferInstanceAs (IsProper (i.left ≫ Z.hom))⟩⟩

private abbrev quotientLeftAction {B : ClosedSubgroup G} (Q : Presentation B) :
    ModObj G.X Q.scheme :=
  let I : ClosedSubgroup G := ⟨G, 𝟙 G, by
    change IsClosedImmersion (𝟙 G.X.left)
    infer_instance⟩
  subgroupQuotientAction (B := I) Q

private theorem quotientLeftAction_on_points {B : ClosedSubgroup G} (Q : Presentation B)
    {Y : SchemeOver k} (g : Y ⟶ G.X) (x : Y ⟶ Q.scheme) :
    lift g x ≫ (quotientLeftAction Q).smul = quotientAct Q g x := by
  change lift g x ≫ quotientAct Q (fst _ _ ≫ 𝟙 G.X) (snd _ _) = _
  simp only [Category.comp_id, quotientAct_comp, lift_fst, lift_snd]

private theorem lift_tensor_comp {X Y X' Y' T : SchemeOver k} (x : T ⟶ X) (y : T ⟶ Y)
    (j : X ⟶ X') (i : Y ⟶ Y') :
    lift x y ≫ (j ⊗ₘ i) = lift (x ≫ j) (y ≫ i) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp

private theorem orbitMap_restrict {C : ClosedSubgroup G} {Z X : SchemeOver k}
    (a : ModObj G.X X) (b : ModObj C.group.X Z) (i : Z ⟶ X)
    (h : b.smul ≫ i = (C.inclusion.hom.hom ⊗ₘ i) ≫ a.smul)
    (z : 𝟙_ (SchemeOver k) ⟶ Z) :
    Specs.SmoothOrbit.orbitMap b z ≫ i =
      C.inclusion.hom.hom ≫ Specs.SmoothOrbit.orbitMap a (z ≫ i) := by
  simp only [Specs.SmoothOrbit.orbitMap, Category.assoc, h, ← Category.assoc
    (lift (𝟙 C.group.X) (toUnit C.group.X ≫ z)), lift_tensor_comp,
    Category.id_comp, Category.comp_id, comp_lift_assoc, comp_toUnit_assoc, Category.assoc]

private theorem identity_orbit_stabilizer {C B : ClosedSubgroup G} {Z : SchemeOver k}
    (Q : Presentation B) (b : ModObj C.group.X Z) (i : Z ⟶ Q.scheme) [Mono i]
    (hi : b.smul ≫ i = (C.inclusion.hom.hom ⊗ₘ i) ≫ (quotientLeftAction Q).smul)
    (z : 𝟙_ (SchemeOver k) ⟶ Z) (hz : z ≫ i = η[G.X] ≫ Q.projection)
    (D : ClosedSubgroup C.group) (hD : IsCentralizerIntersection C B D) :
    RepresentsSubgroup D (fun _ g ↦ Stabilizes b.smul z g) := by
  letI : Mono C.inclusion.hom.hom := mono_over _ C.isClosedImmersion
  intro T g
  have he : Stabilizes b.smul z g ↔
      (g ≫ C.inclusion.hom.hom) ∈ SubgroupSections B T := by
    unfold Stabilizes
    rw [← cancel_mono i, Category.assoc, hi, ← Category.assoc, lift_tensor_comp,
      Category.assoc (toUnit T), hz, ← Category.assoc (toUnit T),
      show toUnit T ≫ η[G.X] = (1 : T ⟶ G.X) from MonObj.comp_one _,
      quotientLeftAction_on_points, quotientAct_projection, mul_one]
    rw [eq_comm]
    simpa only [inv_one, one_mul] using (projection_eq_iff Q (1 : T ⟶ G.X)
      (g ≫ C.inclusion.hom.hom))
  change Stabilizes b.smul z g ↔ ∃ d : T ⟶ D.group.X, d ≫ D.inclusion.hom.hom = g
  rw [he]
  constructor
  · intro hg
    have hg' : g ≫ C.inclusion.hom.hom ∈ SubgroupSections (subgroupOfSubgroup C D) T :=
      (hD _ _).mpr (fun H hH ↦ by
        rcases Set.mem_insert_iff.mp hH with rfl | hH
        · exact ⟨g, rfl⟩
        · obtain rfl := Set.mem_singleton_iff.mp hH
          exact hg)
    change ∃ d : T ⟶ D.group.X,
      d ≫ (D.inclusion.hom.hom ≫ C.inclusion.hom.hom) = g ≫ C.inclusion.hom.hom at hg'
    obtain ⟨d, hd⟩ := hg'
    exact ⟨d, (cancel_mono C.inclusion.hom.hom).mp (by
      simpa only [Category.assoc] using hd)⟩
  · rintro ⟨d, hd⟩
    apply (hD _ _).mp ?_ B (by simp)
    exact ⟨d, by
      change d ≫ D.inclusion.hom.hom ≫ C.inclusion.hom.hom = _
      rw [← Category.assoc, hd]⟩

private theorem fixedLocusOrbits_proof : FixedLocusOrbits.{u} := by
  intro k _ _ A hs hc T S ht hS hst C hC B hb htb Q
  let a := quotientLeftAction Q
  let aS := restrictGroupAction S.inclusion a
  have ha : (𝟙 A.val.X ⊗ₘ Q.projection) ≫ a.smul = μ[A.val.X] ≫ Q.projection := by
    have he : 𝟙 A.val.X ⊗ₘ Q.projection =
        lift (fst A.val.X A.val.X) (snd A.val.X A.val.X ≫ Q.projection) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [he, quotientLeftAction_on_points, quotientAct_projection, MonObj.mul_eq_mul]
  have hproper : IsProper Q.scheme.hom := by
    obtain ⟨N, R, hN, hp⟩ := closed_flag_quotient_proper
      GeometricBorelConjugacy.closedFlagOrbitExists GeometricBorelConjugacy.closedFlagStabilizerIsBorel
      A hs hc
    obtain ⟨g, hg⟩ := GeometricBorelConjugacy.borelsConjugate A hs hc B N hb hN
    exact proper_of_conjugate_quotient g hg Q R hp
  letI := hproper
  obtain ⟨Z, i, hi, hrep⟩ := fixedPointScheme k (closedSubgroupAlgebraicGroup S)
    Q.scheme aS inferInstance inferInstance inferInstance
  obtain ⟨b, hb'⟩ := centralizer_action hC a i hi hrep
  letI := hi
  letI : Mono i := mono_over _ hi
  have hZ : IsProper Z.hom := by rw [← Over.w i]; infer_instance
  let C' := closedSubgroupAlgebraicGroup C
  have hCs := (centralizer_geometry A hs hc S C hS hC).1
  have horbit (z : 𝟙_ (SchemeOver k) ⟶ Z) :
      Smooth (Specs.SmoothOrbit.orbitMap b z).left := by
    obtain ⟨H, ⟨h⟩, htorus⟩ := torus_coordinates (closedSubgroupAlgebraicGroup S) hS
    obtain ⟨n, ⟨t⟩⟩ := split_of_torus (D := closedSubgroupAlgebraicGroup S) ⟨H, ⟨h⟩, htorus⟩
    obtain ⟨d₀⟩ := DiagonalizableGroups.diagonalIntegerPowers k (ULift.{u} (Fin n))
    let e := d₀ ≪≫ t.symm
    let d := e.hom ≫ S.inclusion
    let aD := restrictGroupAction d a
    let f := Specs.SmoothOrbit.orbitMap a (z ≫ i)
    have ht' (Y : SchemeOver k) (y : Y ⟶ Q.scheme) :
        IsFixedBy aD.smul y ↔ IsFixedBy aS.smul y := by
      have he : aD.smul = (e.hom.hom.hom ▷ Q.scheme) ≫ aS.smul := by
        change ((e.hom.hom.hom ≫ S.inclusion.hom.hom) ▷ Q.scheme) ≫ a.smul = _
        rw [comp_whiskerRight_assoc]
        rfl
      rw [he]
      exact isFixedBy_groupIso ((Grp.forget _).mapIso e) aS.smul y
    have hf : Smooth f.left := by
      obtain ⟨g, hg⟩ := rationalLift Q.projection Q.surjective
        (by letI := Q.finitePresentation; infer_instance) (z ≫ i)
      have he : f = (rightTranslation g).hom ≫ Q.projection := by
        rw [show f = Specs.SmoothOrbit.orbitMap a (g ≫ Q.projection) by rw [hg]]
        unfold Specs.SmoothOrbit.orbitMap
        rw [quotientLeftAction_on_points, ← Category.assoc (toUnit A.val.X),
          quotientAct_projection]
        rfl
      haveI : IsIso (rightTranslation g).hom.left :=
        (Over.forget _).map_isIso (rightTranslation g).hom
      haveI : Smooth Q.projection.left := quotientSmooth A Q hb.1.1
      rw [he, Over.comp_left]
      infer_instance
    have hfix : IsFixedBy aD.smul (z ≫ i) :=
      (ht' _ _).mpr ((hrep _ _).mpr ⟨z, rfl⟩)
    apply smooth_map_on_fixed_schemes (M := Multiplicative (ULift.{u} (Fin n) → ℤ))
      (conjugationAction d) aD f (Specs.SmoothOrbit.orbitMap b z) C.inclusion.hom.hom i
      C.isClosedImmersion hi A.property.1 C'.property.2.1 inferInstance hZ.toLocallyOfFiniteType hf
      (orbit_conjugation_equivariant d a (z ≫ i) hfix) (orbitMap_restrict a b i hb' z)
    · intro Y g
      exact (isFixedBy_conjugation_iff d g).trans
        ((centralizes_precomp_iso e S.inclusion g).trans (hC _ _))
    · exact fun Y g ↦ (ht' Y g).trans (hrep Y g)
  obtain ⟨hsm, hO⟩ := proper_orbits_of_smooth_maps C' b hCs hZ horbit
  refine ⟨a, Z, i, b, ha, hi, hrep, hsm, hb', hO, ?_⟩
  intro D hD P
  have hz₀ : IsFixedBy aS.smul (η[A.val.X] ≫ Q.projection) := by
    apply (fixed_iff_families _ _).mpr
    intro Y s y
    have h₁ : y ≫ η[A.val.X] = (1 : Y ⟶ A.val.X) := by
      rw [toUnit_unique y (toUnit Y)]
      exact MonObj.comp_one _
    change (lift s (y ≫ η[A.val.X] ≫ Q.projection) ≫ (S.inclusion.hom.hom ▷ Q.scheme)) ≫
      a.smul = _
    rw [lift_whiskerRight, quotientLeftAction_on_points, ← Category.assoc y, h₁,
      quotientAct_projection, mul_one]
    apply ((projection_eq_iff Q (1 : Y ⟶ A.val.X) (s ≫ S.inclusion.hom.hom)).mpr ?_).symm
    simpa only [inv_one, one_mul] using
      sections_of_subgroupOf (subgroupOf_trans hst htb)
        (show s ≫ S.inclusion.hom.hom ∈ SubgroupSections S Y from ⟨s, rfl⟩)
  obtain ⟨z, hz⟩ := (hrep _ _).mp hz₀
  obtain ⟨O⟩ := hO z
  haveI := O.smoothProjection
  haveI := O.openImmersion
  obtain ⟨e, he⟩ := SmoothOrbit.orbitQuotient k C.group Z O.scheme b z O.inclusion O.projection D
    (Over.mono_of_mono_left _) O.factors inferInstance O.surjectiveProjection inferInstance
    (identity_orbit_stabilizer Q b i hb' z hz D hD)
  exact ⟨z, O, compareRepresentatives P e, hz, compareRepresentatives_projection P _ e he⟩

theorem fixedLocusOrbits_conditional
    (_ : SolvableRadicalFromBorelIntersection.{u}) (_ : UnipotentOrbitsClosed.{u})
    (_ : UnipotentRadicalFromBorelIntersection.{u}) : FixedLocusOrbits.{u} :=
  fixedLocusOrbits_proof

theorem centralizerBorel_conditional
    (_ : SolvableRadicalFromBorelIntersection.{u}) (_ : UnipotentOrbitsClosed.{u})
    (_ : UnipotentRadicalFromBorelIntersection.{u}) : CentralizerBorel.{u} :=
  centralizerBorel_of_fixedLocusOrbits fixedLocusOrbits_proof

theorem unipotentRadicalInclusion_conditional
    (hsolv : SolvableRadicalFromBorelIntersection.{u}) (_ : UnipotentOrbitsClosed.{u})
    (hunip : UnipotentRadicalFromBorelIntersection.{u}) : UnipotentRadicalInclusion.{u} :=
  unipotentRadicalInclusion_of_centralizerBorel
    (centralizerBorel_of_fixedLocusOrbits fixedLocusOrbits_proof) hsolv hunip

theorem centralizerReductive_conditional
    (hsolv : SolvableRadicalFromBorelIntersection.{u}) (horbit : UnipotentOrbitsClosed.{u})
    (hunip : UnipotentRadicalFromBorelIntersection.{u}) : CentralizerReductive.{u} :=
  centralizerReductive_of_radicalInclusion
    (unipotentRadicalInclusion_conditional hsolv horbit hunip)

end

end LinearAlgebraicGroups.Reductive.SubtorusCentralizer

universe v8_closure_6d2d0358218046a7_u0
theorem _root_.«LinearAlgebraicGroups».«Reductive».«SubtorusCentralizer».«centralizerBorel» : _root_.«LinearAlgebraicGroups».«Specs».«SubtorusCentralizer».«CentralizerBorel».{v8_closure_6d2d0358218046a7_u0} :=
  @_root_.«LinearAlgebraicGroups».«Reductive».«SubtorusCentralizer».«centralizerBorel_conditional».{v8_closure_6d2d0358218046a7_u0} (@_root_.«LinearAlgebraicGroups».«Reductive».«UnipotentRadicalIntersection».«solvableRadicalFromBorelIntersection».{v8_closure_6d2d0358218046a7_u0}) (@_root_.«LinearAlgebraicGroups».«Reductive».«UnipotentRadicalIntersection».«unipotentOrbitsClosed».{v8_closure_6d2d0358218046a7_u0}) (@_root_.«LinearAlgebraicGroups».«Reductive».«UnipotentRadicalIntersection».«unipotentRadicalFromBorelIntersection».{v8_closure_6d2d0358218046a7_u0})
theorem _root_.«LinearAlgebraicGroups».«Reductive».«SubtorusCentralizer».«centralizerReductive» : _root_.«LinearAlgebraicGroups».«Specs».«SubtorusCentralizer».«CentralizerReductive».{v8_closure_6d2d0358218046a7_u0} :=
  @_root_.«LinearAlgebraicGroups».«Reductive».«SubtorusCentralizer».«centralizerReductive_conditional».{v8_closure_6d2d0358218046a7_u0} (@_root_.«LinearAlgebraicGroups».«Reductive».«UnipotentRadicalIntersection».«solvableRadicalFromBorelIntersection».{v8_closure_6d2d0358218046a7_u0}) (@_root_.«LinearAlgebraicGroups».«Reductive».«UnipotentRadicalIntersection».«unipotentOrbitsClosed».{v8_closure_6d2d0358218046a7_u0}) (@_root_.«LinearAlgebraicGroups».«Reductive».«UnipotentRadicalIntersection».«unipotentRadicalFromBorelIntersection».{v8_closure_6d2d0358218046a7_u0})
theorem _root_.«LinearAlgebraicGroups».«Reductive».«SubtorusCentralizer».«fixedLocusOrbits» : _root_.«LinearAlgebraicGroups».«Specs».«SubtorusCentralizer».«FixedLocusOrbits».{v8_closure_6d2d0358218046a7_u0} :=
  @_root_.«LinearAlgebraicGroups».«Reductive».«SubtorusCentralizer».«fixedLocusOrbits_conditional».{v8_closure_6d2d0358218046a7_u0} (@_root_.«LinearAlgebraicGroups».«Reductive».«UnipotentRadicalIntersection».«solvableRadicalFromBorelIntersection».{v8_closure_6d2d0358218046a7_u0}) (@_root_.«LinearAlgebraicGroups».«Reductive».«UnipotentRadicalIntersection».«unipotentOrbitsClosed».{v8_closure_6d2d0358218046a7_u0}) (@_root_.«LinearAlgebraicGroups».«Reductive».«UnipotentRadicalIntersection».«unipotentRadicalFromBorelIntersection».{v8_closure_6d2d0358218046a7_u0})
theorem _root_.«LinearAlgebraicGroups».«Reductive».«SubtorusCentralizer».«unipotentRadicalInclusion» : _root_.«LinearAlgebraicGroups».«Specs».«SubtorusCentralizer».«UnipotentRadicalInclusion».{v8_closure_6d2d0358218046a7_u0} :=
  @_root_.«LinearAlgebraicGroups».«Reductive».«SubtorusCentralizer».«unipotentRadicalInclusion_conditional».{v8_closure_6d2d0358218046a7_u0} (@_root_.«LinearAlgebraicGroups».«Reductive».«UnipotentRadicalIntersection».«solvableRadicalFromBorelIntersection».{v8_closure_6d2d0358218046a7_u0}) (@_root_.«LinearAlgebraicGroups».«Reductive».«UnipotentRadicalIntersection».«unipotentOrbitsClosed».{v8_closure_6d2d0358218046a7_u0}) (@_root_.«LinearAlgebraicGroups».«Reductive».«UnipotentRadicalIntersection».«unipotentRadicalFromBorelIntersection».{v8_closure_6d2d0358218046a7_u0})
