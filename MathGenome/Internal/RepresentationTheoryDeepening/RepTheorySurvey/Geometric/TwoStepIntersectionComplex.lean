import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TwoStepIntersectionComplex
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TwoStepLocalCohomology
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeAndTwoStep
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionBundle
import Mathlib.CategoryTheory.Filtered.Final

import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionSurface
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TwoStepLocalCohomology
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated Opposite TopologicalSpace Topology
open scoped ZeroObject

namespace RepTheorySurvey.Geometric.TwoStepIntersectionComplex

open Analytic Analytic.IntersectionComplex LocalSheaf
open LatticeModelSpecs MinusculeAndTwoStepSpecs
open TwoStepIntersectionComplexSpecs
open TwoStepLocalCohomologySpecs

open private colengthHomeomorphShort from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeAndTwoStep
open private closedShriekOpenIso embeddingIsoOfRange embeddingIsoOfRange_comp
  pullbackStalkIso pullbackCohomologyIso pullbackIsLE plusIsLE_iff plusIsGE_iff strictAttachmentOfBound
  pullbackEquivalence closedInverseAdjunction
  locallyConstantFiniteRank_of_iso zero_locallyConstantFiniteRank
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

private def constColimitIso {J : Type*} [Category* J] [IsConnected J] (V : Coeff.{0}) :
    colimit ((Functor.const J).obj V) ≅ V :=
  (colimit.isColimit _).coconePointUniqueUpToIso (isColimitConstCocone J V)

private instance : Nonempty PositiveRadius := ⟨⟨1, by norm_num⟩⟩

private def radialNhds (c : RadialChart)
    (h : (nhds c.vertex).HasBasis (fun _ : PositiveRadius ↦ True)
      (fun r ↦ (c.balls.obj r : Set ChartSpace))) : PositiveRadius ⥤ OpenNhds c.vertex :=
  Monotone.functor (f := fun r ↦ ⟨c.balls.obj r, mem_of_mem_nhds (h.mem_of_mem trivial)⟩)
    (fun _ _ le ↦ (c.balls.map (homOfLE le)).le)

private theorem radialNhds_initial (c : RadialChart) (h) : (radialNhds c h).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered
  · intro V
    obtain ⟨r, _, hr⟩ := h.mem_iff.mp (V.1.isOpen.mem_nhds V.2)
    exact ⟨r, ⟨homOfLE hr⟩⟩
  · intro V r i j
    exact ⟨r, 𝟙 r, Subsingleton.elim _ _⟩

private def radialStalkIso (c : RadialChart)
    (h : (nhds c.vertex).HasBasis (fun _ : PositiveRadius ↦ True)
      (fun r ↦ (c.balls.obj r : Set ChartSpace)))
    (P : ChartSpace.Presheaf Coeff.{0})
    (V : Coeff.{0}) (e : c.balls.op ⋙ P ≅ (Functor.const PositiveRadiusᵒᵖ).obj V) :
    stalkColimit P c.vertex ≅ V := by
  let R := radialNhds c h
  letI : R.Initial := radialNhds_initial c h
  letI : R.op.Final := Functor.final_of_initial_op R.op
  let d : R.op ⋙ (OpenNhds.inclusion c.vertex).op ⋙ P ≅ c.balls.op ⋙ P :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro r s f
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      apply congrArg P.map
      exact Subsingleton.elim _ _)
  exact (Functor.Final.colimitIso R.op ((OpenNhds.inclusion c.vertex).op ⋙ P)).symm ≪≫
    HasColimit.isoOfNatIso d ≪≫
    HasColimit.isoOfNatIso e ≪≫ constColimitIso V

/-- Compute the costalk by cofinal restriction to the radial opens. -/
private theorem chartCostalk (c : RadialChart)
    (h : (nhds c.vertex).HasBasis (fun _ : PositiveRadius ↦ True)
      (fun r ↦ (c.balls.obj r : Set ChartSpace)))
    (hs : TwoStepLocalCohomologySpecs.Expected.RadialSheafCohomology)
    (hg : TwoStepLocalCohomologySpecs.Expected.RadialSingularCohomology) (q : ℤ) :
    Nonempty (((DerivedCategory.Plus.homologyFunctor _ q ⋙
      stalk (⟨c.vertex, rfl⟩ : ({c.vertex} : Set ChartSpace))).obj
      ((derivedExtraordinaryInverseImage c.closedVertex).obj
        (sheafInDegreeZero (rational ChartSpace)))) ≅ cohomologyValue {4} q) := by
  obtain ⟨_, _, g, _⟩ := hg c
  obtain ⟨_, ⟨d⟩⟩ := (hs c).2.2 q
  obtain ⟨e⟩ := DerivedLocalSheaves.costalk c.closedVertex ⟨c.vertex, rfl⟩ q
    (sheafInDegreeZero (rational ChartSpace))
  exact ⟨e ≪≫ radialStalkIso c h _ _ (Functor.isoWhiskerLeft c.balls.op d.symm ≪≫ g q)⟩

private def rationalRestrictionZero {A B : TopCat.{0}} (k : A ⟶ B) :
    (boundedBelowInverseImage k).obj (sheafInDegreeZero (rational B)) ≅
      sheafInDegreeZero (rational A) :=
  by
  apply ObjectProperty.isoMk _
  change (derivedInverseImage k).obj ((DerivedCategory.singleFunctor _ 0).obj (rational B)) ≅
    (DerivedCategory.singleFunctor _ 0).obj (rational A)
  let e := ((inverseImage k).mapDerivedCategorySingleFunctor 0).app (rational B)
  change (derivedInverseImage k).obj ((DerivedCategory.singleFunctor _ 0).obj (rational B)) ≅
    (DerivedCategory.singleFunctor _ 0).obj ((inverseImage k).obj (rational B)) at e
  exact e ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso (rationalPullback k)

private theorem unshiftedVertexCostalk (h : scalarPoint ∈ colength 2)
    (hx : IsClosed ({vertex h} : Set X))
    (hb : TwoStepLocalCohomologySpecs.Expected.RadialNeighborhoodBasis)
    (hs : TwoStepLocalCohomologySpecs.Expected.RadialSheafCohomology)
    (hg : TwoStepLocalCohomologySpecs.Expected.RadialSingularCohomology) (q : ℤ) :
    Nonempty (vertexCostalk (vertex h) hx (sheafInDegreeZero (rational X)) q ≅
      cohomologyValue {4} q) := by
  let x := vertex h
  obtain ⟨c, hc, _⟩ := hb
  let E : Colength 2 ≃ₜ NilpotentConeChartSpecs.ShortLatticeStage := colengthHomeomorphShort 2
  let k : ChartSpace ⟶ X := TopCat.ofHom
    ⟨fun y ↦ E.symm y.val, E.symm.continuous.comp continuous_subtype_val⟩
  have hk : IsOpenEmbedding k := E.symm.isOpenEmbedding.comp c.isOpen.isOpenEmbedding_subtypeVal
  have hv : k c.vertex = x := Subtype.ext c.vertex_eq
  let m := closedInclusion ({c.vertex} : Set ChartSpace)
  let i := closedInclusion ({x} : Set X)
  have hm : IsEmbedding (m ≫ k) := hk.isEmbedding.comp IsEmbedding.subtypeVal
  have hrange : Set.range i = Set.range (m ≫ k) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨⟨c.vertex, rfl⟩, hv.trans (Set.mem_singleton_iff.mp z.property).symm⟩
    · rintro ⟨z, rfl⟩
      have hz : (z : ChartSpace) = c.vertex := Set.mem_singleton_iff.mp z.property
      exact ⟨⟨x, rfl⟩, (congrArg k hz).trans hv |>.symm⟩
  let v := embeddingIsoOfRange i (m ≫ k) IsEmbedding.subtypeVal hm hrange
  have hv' : v.hom ≫ m ≫ k = i := embeddingIsoOfRange_comp i _ _ _ hrange
  let z : ({x} : Set X) := ⟨x, rfl⟩
  have hz : v.hom z = (⟨c.vertex, rfl⟩ : ({c.vertex} : Set ChartSpace)) :=
    Subtype.ext (Set.mem_singleton_iff.mp (v.hom z).property)
  let F := sheafInDegreeZero (rational X)
  let S := derivedExtraordinaryInverseImage c.closedVertex
  let e := closedShriekOpenIso hx c.closedVertex k hk v hv' F
  refine ⟨((DerivedCategory.Plus.homologyFunctor _ q) ⋙ stalk z).mapIso e ≪≫
    pullbackStalkIso v.hom (S.obj ((boundedBelowInverseImage k).obj F)) q z ≪≫ ?_⟩
  rw [hz]
  let H := DerivedCategory.Plus.homologyFunctor (Sheaves (TopCat.of ({c.vertex} : Set ChartSpace))) q ⋙
    stalk (⟨c.vertex, rfl⟩ : ({c.vertex} : Set ChartSpace))
  change H.obj (S.obj ((boundedBelowInverseImage k).obj F)) ≅ _
  exact H.mapIso (S.mapIso (rationalRestrictionZero k)) ≪≫
    Classical.choice (chartCostalk c hc hs hg q)

private def cohomologyOfShiftedPlus {Y : TopCat.{0}} (G : BoundedBelow Y) (q d : ℤ) :
    (DerivedCategory.Plus.homologyFunctor _ q).obj (G⟦d⟧) ≅
      (DerivedCategory.Plus.homologyFunctor _ (q + d)).obj G := by
  let I := DerivedCategory.Plus.ι (C := Sheaves Y)
  let e := (I.commShiftIso d).app G
  change (cohomology Y q).obj (I.obj (G⟦d⟧)) ≅ (cohomology Y (q + d)).obj G.obj
  exact (cohomology Y q).mapIso e ≪≫ (shiftCohomology Y q d).app G.obj

private def shiftedPlusIso (Y : TopCat.{0}) :
    shiftedConstant Y 2 ≅ (sheafInDegreeZero (rational Y))⟦(2 : ℤ)⟧ := by
  let I := DerivedCategory.Plus.ι (C := Sheaves Y)
  let e := (I.commShiftIso (2 : ℤ)).app (sheafInDegreeZero (rational Y))
  exact I.preimageIso e.symm

private theorem shiftedVertexCostalk (h : scalarPoint ∈ colength 2)
    (hx : IsClosed ({vertex h} : Set X))
    (hb : TwoStepLocalCohomologySpecs.Expected.RadialNeighborhoodBasis)
    (hs : TwoStepLocalCohomologySpecs.Expected.RadialSheafCohomology)
    (hg : TwoStepLocalCohomologySpecs.Expected.RadialSingularCohomology) :
    HasSingleDegree (vertexCostalk (vertex h) hx (shiftedConstant X 2)) 2 := by
  let x := vertex h
  let R := derivedExtraordinaryInverseImage hx
  let F := sheafInDegreeZero (rational X)
  letI : R.CommShift ℤ := by
    unfold R derivedExtraordinaryInverseImage
    infer_instance
  have iso (q : ℤ) : Nonempty (vertexCostalk x hx (shiftedConstant X 2) q ≅
      cohomologyValue {4} (q + 2)) := by
    obtain ⟨d⟩ := unshiftedVertexCostalk h hx hb hs hg (q + 2)
    let z : ({x} : Set X) := ⟨x, rfl⟩
    let H := DerivedCategory.Plus.homologyFunctor (Sheaves (TopCat.of ({x} : Set X))) q
    let e : R.obj (shiftedConstant X 2) ≅ (R.obj F)⟦(2 : ℤ)⟧ :=
      R.mapIso (shiftedPlusIso X) ≪≫ (R.commShiftIso (2 : ℤ)).app F
    let e₁ := (H ⋙ stalk z).mapIso e
    let e₂ := (stalk z).mapIso (cohomologyOfShiftedPlus (R.obj F) q 2)
    exact ⟨e₁ ≪≫ e₂ ≪≫ d⟩
  refine ⟨?_, fun q hq ↦ ?_⟩
  · simpa [cohomologyValue] using iso 2
  · have hq' : q + 2 ≠ 4 := by omega
    obtain ⟨e⟩ := iso q
    have hz : IsZero (cohomologyValue {4} (q + 2)) := by
      simpa [cohomologyValue, hq'] using (isZero_zero Coeff.{0})
    exact hz.of_iso e

private def rationalStalk {Y : TopCat.{0}} (y : Y) : (stalk y).obj (rational Y) ≅ ModuleCat.of ℚ ℚ := by
  let Q : Coeff.{0} := ModuleCat.of ℚ (ULift.{0} ℚ)
  let P : Y.Presheaf Coeff.{0} := (Functor.const _).obj Q
  let a := TopCat.Presheaf.stalkFunctor Coeff.{0} y
  letI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso y Coeff.{0} P
  exact (asIso (a.map (toSheafify (Opens.grothendieckTopology Y) P))).symm ≪≫
    constColimitIso Q ≪≫ (ULift.moduleEquiv : ULift.{0} ℚ ≃ₗ[ℚ] ℚ).toModuleIso

private theorem shiftedConstantIsLE (Y : TopCat.{0}) : (shiftedConstant Y 2).IsLE (-2) := by
  apply (DerivedCategory.Plus.isLE_ι_obj_iff _ _).mp
  let F := (DerivedCategory.singleFunctor (Sheaves Y) 0).obj (rational Y)
  exact (DerivedCategory.TStructure.t (C := Sheaves Y)).isLE_shift F 0 2 (-2) (by decide)

private theorem shiftedCohomologyZero (Y : TopCat.{0}) (q : ℤ) (hq : q ≠ -2) :
    IsZero ((cohomology Y q).obj (shiftedConstant Y 2).obj) := by
  rcases lt_or_gt_of_ne hq with h | h
  · let F := (DerivedCategory.singleFunctor (Sheaves Y) 0).obj (rational Y)
    have hge : (shiftedConstant Y 2).obj.IsGE (-2) :=
      (DerivedCategory.TStructure.t (C := Sheaves Y)).isGE_shift F 0 2 (-2) (by decide)
    exact (DerivedCategory.isGE_iff _ _).mp hge q h
  · exact (DerivedCategory.isLE_iff _ _).mp
      ((DerivedCategory.Plus.isLE_ι_obj_iff _ _).mpr (shiftedConstantIsLE Y)) q h

private def shiftedCohomologyAtDegree (Y : TopCat.{0}) :
    (cohomology Y (-2)).obj (shiftedConstant Y 2).obj ≅ rational Y :=
  let F := (DerivedCategory.singleFunctor (Sheaves Y) 0).obj (rational Y)
  let e : (cohomology Y (-2)).obj (shiftedConstant Y 2).obj ≅ (cohomology Y 0).obj F :=
    (shiftCohomology Y (-2) 2).app F
  e ≪≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso (Sheaves Y) 0).app (rational Y)

private theorem shiftedVertexStalk (x : X) :
    HasSingleDegree (vertexStalk x (shiftedConstant X 2)) (-2) :=
  ⟨⟨(stalk x).mapIso (shiftedCohomologyAtDegree X) ≪≫ rationalStalk x⟩,
    fun q hq ↦ (stalk x).map_isZero (shiftedCohomologyZero X q hq)⟩

private theorem boundary_eq_singleton (x : X) (hx : IsClosed ({x} : Set X)) :
    boundary (inclusion x hx) = ({x} : Set X) := by
  have e : Set.range (inclusion x hx) = ({x} : Set X)ᶜ := Subtype.range_coe
  exact congrArg Set.compl e |>.trans (compl_compl _)

private theorem shiftedStrict (x : X) (hx : IsClosed ({x} : Set X))
    (hc : HasSingleDegree (vertexCostalk x hx (shiftedConstant X 2)) 2) :
    IsStrictExtension (U x hx).isOpenEmbedding 0 (shiftedConstant X 2) := by
  let K := shiftedConstant X 2
  have hle : K.IsLE (-1) := (plusIsLE_iff K _).mpr
    (fun q hq ↦ shiftedCohomologyZero X q (by omega))
  refine ⟨pullbackIsLE _ K _ hle, ?_⟩
  have aux (Z : Set X) (hZ : IsClosed Z) (h : Z = {x}) :
      ((derivedExtraordinaryInverseImage hZ).obj K).IsGE 1 := by
    subst Z
    apply (plusIsGE_iff _ _).mpr
    intro q hq
    apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
    intro y
    have hy : y = ⟨x, rfl⟩ := Subtype.ext (Set.mem_singleton_iff.mp y.property)
    subst y
    exact hc.2 q (by omega)
  exact aux _ _ (boundary_eq_singleton x hx)

private theorem strictSurface (x : X) (hx : IsClosed ({x} : Set X)) :
    let j := inclusion x hx
    let hj : IsOpenEmbedding j := (U x hx).isOpenEmbedding
    let F := shifted x hx
    IsStrictExtension hj 0 (surface x hx) ∧
      ∀ a : boundedBelowInverseImage j ⊣ derivedDirectImage j,
        IsIso ((boundedBelowInverseImage j).map ((attachmentInclusion j hj 0).app F) ≫
          a.counit.app F) :=
  strictAttachmentOfBound (inclusion x hx) (U x hx).isOpenEmbedding 0 (shifted x hx)
    ((plusIsLE_iff _ _).mpr fun q hq ↦ shiftedCohomologyZero _ q (by omega))

/-- Lift the coefficient identification uniquely through restriction of strict extensions. -/
private theorem identifySurface (x : X) (hx : IsClosed ({x} : Set X))
    (hc : HasSingleDegree (vertexCostalk x hx (shiftedConstant X 2)) 2)
    (a : boundedBelowInverseImage (inclusion x hx) ⊣ derivedDirectImage (inclusion x hx)) :
    let j := inclusion x hx
    let hj : IsOpenEmbedding j := (U x hx).isOpenEmbedding
    let F := shifted x hx
    let K := shiftedConstant X 2
    ∃ e : K ≅ surface x hx,
      e.hom ≫ (attachmentInclusion j hj 0).app F =
        a.homEquiv K F (shiftedRestriction x hx).hom ∧
      (boundedBelowInverseImage j).map e.hom ≫
        (boundedBelowInverseImage j).map ((attachmentInclusion j hj 0).app F) ≫
        a.counit.app F = (shiftedRestriction x hx).hom := by
  dsimp only
  let j := inclusion x hx
  let hj : IsOpenEmbedding j := (U x hx).isOpenEmbedding
  let F := shifted x hx
  let K := shiftedConstant X 2
  obtain ⟨he, ha⟩ := strictSurface x hx
  let L := boundedBelowInverseImage j
  let α := L.map ((attachmentInclusion j hj 0).app F) ≫ a.counit.app F
  haveI : IsIso α := ha a
  let β := asIso α
  let A : (show ObjectProperty (BoundedBelow X) from IsStrictExtension hj 0).FullSubcategory :=
    ⟨K, shiftedStrict x hx hc⟩
  let B : (show ObjectProperty (BoundedBelow X) from IsStrictExtension hj 0).FullSubcategory :=
    ⟨surface x hx, he⟩
  obtain ⟨ff⟩ := MiddleExtension.strictRestrictionFullyFaithful j hj 0
  let r : (strictRestriction hj 0).obj A ≅ (strictRestriction hj 0).obj B :=
    shiftedRestriction x hx ≪≫ β.symm
  let E := ff.preimageIso r
  let e := (ObjectProperty.ι _).mapIso E
  have hm : L.map e.hom = r.hom := ff.map_preimage r.hom
  have hopen : L.map e.hom ≫ α = (shiftedRestriction x hx).hom := by
    rw [hm]
    change r.hom ≫ β.hom = _
    simp only [r, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨e, ?_, hopen⟩
  apply (a.homEquiv K F).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  exact hopen

private theorem singleDegreeOfIso {H G : ℤ → Coeff.{0}} {d : ℤ}
    (e : ∀ q, H q ≅ G q) (h : HasSingleDegree H d) : HasSingleDegree G d :=
  ⟨Nonempty.map (fun i ↦ (e d).symm ≪≫ i) h.1, fun q hq ↦ (h.2 q hq).of_iso (e q).symm⟩

private def univShriekIso (Y : TopCat.{0}) :
    derivedExtraordinaryInverseImage (isClosed_univ (X := Y)) ≅
      boundedBelowInverseImage (closedInclusion (Set.univ : Set Y)) := by
  let v : TopCat.of (Set.univ : Set Y) ≅ Y := TopCat.isoOfHomeo (Homeomorph.Set.univ Y)
  let V := pullbackEquivalence v
  let h : IsClosed (Set.univ : Set Y) := isClosed_univ
  let a := closedInverseAdjunction h
  let b := DerivedLocalSheaves.derivedExtraordinaryAdjunctionData h
  let e : closedExtensionPlus h ≅ V.inverse := a.rightAdjointUniq V.toAdjunction
  exact (b.ofNatIsoLeft e).rightAdjointUniq V.symm.toAdjunction

private theorem locallyConstantRational (Y : TopCat.{0}) : LocallyConstantFiniteRank (rational Y) := by
  intro y
  refine ⟨⊤, trivial, ModuleCat.of ℚ (ULift.{0} ℚ), ?_, ⟨rationalPullback (openInclusion ⊤)⟩⟩
  exact Module.Finite.of_surjective
    (ULift.moduleEquiv : ULift.{0} ℚ ≃ₗ[ℚ] ℚ).symm.toLinearMap
    (ULift.moduleEquiv : ULift.{0} ℚ ≃ₗ[ℚ] ℚ).symm.surjective

private theorem perverseOfNormalized (x : X) (hx : IsClosed ({x} : Set X))
    (G : BoundedBelow X) (e : G ≅ shiftedConstant X 2)
    (hc : HasSingleDegree (vertexCostalk x hx (shiftedConstant X 2)) 2) :
    IsMiddlePerverse (stratification x hx) G.obj := by
  let Q := stratification x hx
  let c (q : ℤ) := (DerivedCategory.Plus.homologyFunctor _ q).mapIso e
  have hz (q : ℤ) (hq : q ≠ -2) : IsZero ((cohomology X q).obj G.obj) :=
    (shiftedCohomologyZero X q hq).of_iso (c q)
  refine ⟨⟨(Set.finite_singleton (-2 : ℤ)).subset ?_, ?_⟩, G.property, ?_⟩
  · intro q hq
    exact Set.mem_singleton_iff.mpr (not_ne_iff.mp (fun h ↦ hq (hz q h)))
  · intro s q
    let f := (Q.stratum s).inclusion
    by_cases hq : q = -2
    · subst q
      have d : (inverseImage f).obj ((cohomology X (-2)).obj G.obj) ≅
          rational (Q.stratum s).space :=
        (inverseImage f).mapIso (c (-2) ≪≫ shiftedCohomologyAtDegree X) ≪≫ rationalPullback f
      exact locallyConstantFiniteRank_of_iso d.symm (locallyConstantRational _)
    · exact zero_locallyConstantFiniteRank ((inverseImage f).map_isZero (hz q hq))
  · intro s
    constructor
    · intro q hq
      have hd : q ≠ -2 := by
        cases s
        · change (-(0 : ℤ) < q) at hq
          omega
        · change (-(2 : ℤ) < q) at hq
          omega
      exact ((inverseImage (Q.stratum s).inclusion).map_isZero (hz q hd)).of_iso
        (pullbackCohomologyIso (Q.stratum s).inclusion G q)
    · intro q hq
      cases s
      · change q < -(0 : ℤ) at hq
        let S := closedStratum x hx
        let k := openInclusion S.ambientOpen
        let i := closedInclusion ({x} : Set X)
        let m := S.inclusion
        have hi : Set.range i = {x} := Subtype.range_coe
        let h := hi.trans (closedStratum_range x hx).symm
        have hm : IsEmbedding m := S.ambientOpen.isOpenEmbedding.isEmbedding.comp IsEmbedding.subtypeVal
        let v := embeddingIsoOfRange i m IsEmbedding.subtypeVal hm h
        have hv' : v.hom ≫ closedInclusion (X := TopCat.of S.ambientOpen) S.subset ≫ k = i :=
          embeddingIsoOfRange_comp i m IsEmbedding.subtypeVal hm h
        let d := closedShriekOpenIso hx S.closed k S.ambientOpen.isOpenEmbedding v hv' G
        apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
        intro y
        let z : ({x} : Set X) := ⟨x, rfl⟩
        have hz' : v.hom z = y := by
          have hzy : v.inv y = z := Subtype.ext (Set.mem_singleton_iff.mp (v.inv y).property)
          exact (congrArg (fun t : TopCat.of ({x} : Set X) ↦ v.hom t) hzy).symm.trans
            (congrArg (fun f : S.space ⟶ S.space ↦ f y) v.inv_hom_id)
        rw [← hz']
        let J := DerivedCategory.Plus.homologyFunctor (Sheaves (TopCat.of ({x} : Set X))) q ⋙
          stalk (X := TopCat.of ({x} : Set X)) z
        let d' := J.mapIso d ≪≫ pullbackStalkIso v.hom (S.shriek.obj G) q z
        let d'' := J.mapIso ((derivedExtraordinaryInverseImage hx).mapIso e)
        exact (hc.2 q (by omega)).of_iso (d'.symm ≪≫ d'')
      · change q < -(2 : ℤ) at hq
        let S := openStratum x hx
        let A := TopCat.of (U x hx)
        let j := inclusion x hx
        let f := closedInclusion (Set.univ : Set A)
        let ε := (boundedBelowInverseImage j).mapIso e ≪≫ shiftedRestriction x hx
        let d : S.shriek.obj G ≅ (boundedBelowInverseImage f).obj (shifted x hx) :=
          (univShriekIso A).app ((boundedBelowInverseImage j).obj G) ≪≫
            (boundedBelowInverseImage f).mapIso ε
        exact ((inverseImage f).map_isZero (shiftedCohomologyZero A q (by omega))).of_iso
          ((DerivedCategory.Plus.homologyFunctor _ q).mapIso d ≪≫
            pullbackCohomologyIso f (shifted x hx) q)

section Geometry

open AlgebraicGeometry LinearAlgebraicGroups
open LinearAlgebraicGroups.Specs.GrassmannianCharts
open ConvolutionBundleSpecs ConvolutionSurfaceSpecs
open scoped AlgebraicGeometry

open private firstChartSystem secondChartSystem rawIncidence rawInclusion
  rawInclusion_closed rawIncidence_affine incidenceIsoRaw
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionBundle
open private pivotCover from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionBundleCharts

private theorem chartDimension (I : Pivot (Fin 2 × Fin 1) 1) :
    SmoothOfRelativeDimension 1 (chartScheme (k := ℂ) I).hom := by
  let n := Outside I × Inside I
  have hi : Fintype.card (Inside I) = 1 := by
    rw [Fintype.card_coe, I.property]
  have ho : Fintype.card (Outside I) = 1 := by
    rw [Fintype.card_subtype_compl, hi]
    decide
  have hn : Nat.card n = 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, hi, ho]
  let B := CommRingCat.of ℂ
  let e := AffineSpace.SpecIso n B
  have he : e.inv ≫ (𝔸(n; Spec B) ↘ Spec B) = (chartScheme (k := ℂ) I).hom :=
    AffineSpace.SpecIso_inv_over (n := n) B
  rw [← he, MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 1)]
  exact AffineSpace.smoothOfRelativeDimension_of_card_eq _ hn

private theorem projectiveDimension : SmoothOfRelativeDimension 1 projectiveScheme.hom := by
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension 1)
    (pivotCover firstChartSystem)
  intro I
  change SmoothOfRelativeDimension 1 ((firstChartSystem.chart I).left ≫ projectiveScheme.hom)
  let l := firstChartSystem.chart I
  have h : l.left ≫ projectiveScheme.hom = (chartScheme (k := ℂ) I).hom := Over.w l
  exact h.symm ▸ chartDimension I

private theorem productDimension (I : Pivot (Fin 2 × Fin 1) 1) :
    SmoothOfRelativeDimension 2 ((chartScheme (k := ℂ) I) ⨯ projectiveScheme).hom := by
  let A := chartScheme (k := ℂ) I
  let B := projectiveScheme
  let f : A ⨯ B ⟶ B := prod.snd
  have h : IsPullback (prod.fst : A ⨯ B ⟶ A).left f.left A.hom B.hom :=
    Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk prod.fst f) (prodIsProd A B)
  letI : SmoothOfRelativeDimension 1 f.left :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1) h (chartDimension I)
  letI : SmoothOfRelativeDimension 1 B.hom := projectiveDimension
  change SmoothOfRelativeDimension 2 (A ⨯ B).hom
  rw [← Over.w f]
  exact inferInstanceAs (SmoothOfRelativeDimension (1 + 1) (f.left ≫ B.hom))

/-- The projective bundle charts give the relative dimension of the incidence scheme. -/
private theorem incidenceDimension : SmoothOfRelativeDimension 2 incidenceScheme.hom := by
  obtain ⟨e, _, _⟩ := incidenceIsoRaw
  let a : incidenceScheme.left ≅ rawIncidence.left := (Over.forget _).mapIso e
  have hdim : SmoothOfRelativeDimension 2 rawIncidence.hom := by
    let f := rawInclusion ≫ prod.fst
    let O := (pivotCover firstChartSystem).pullback₁ f.left
    obtain ⟨charts, _⟩ := ConvolutionBundleCharts.bundleCharts projectiveBasis twoStepBasis
      firstChartSystem secondChartSystem rawInclusion rawInclusion_closed rawIncidence_affine
    apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension 2) O
    intro I
    obtain ⟨b, _, _⟩ := charts I
    let b₁ := (Over.forget (Spec (CommRingCat.of ℂ))).mapIso b
    let b₂ : (pullback f (firstChartSystem.chart I)).left ≅ O.X I :=
      PreservesPullback.iso (Over.forget _) f (firstChartSystem.chart I)
    have hb₂ : b₂.inv ≫ (pullback.fst f (firstChartSystem.chart I)).left = O.f I :=
      PreservesPullback.iso_inv_fst _ _ _
    let B := (chartScheme (k := ℂ) I) ⨯ projectiveScheme
    have hw : (pullback.fst f (firstChartSystem.chart I)).left ≫ rawIncidence.hom =
        b₁.hom ≫ B.hom :=
      (Over.w (pullback.fst f (firstChartSystem.chart I))).trans (Over.w b.hom).symm
    have h : O.f I ≫ rawIncidence.hom = (b₂.inv ≫ b₁.hom) ≫ B.hom := by
      calc
        _ = b₂.inv ≫ (pullback.fst f (firstChartSystem.chart I)).left ≫ rawIncidence.hom :=
          (congrArg (· ≫ rawIncidence.hom) hb₂.symm).trans (Category.assoc _ _ _)
        _ = _ := (congrArg (b₂.inv ≫ ·) hw).trans (Category.assoc _ _ _).symm
    rw [h, MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 2)]
    exact productDimension I
  rw [← Over.w e.hom]
  change SmoothOfRelativeDimension 2 (a.hom ≫ rawIncidence.hom)
  rwa [MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 2)]

private theorem smoothFromOpenOrbit (h : OpenOrbitIsomorphism) :
    TwoStepIntersectionComplexSpecs.Expected.SmoothOpenOrbit := by
  obtain ⟨p, W, hp, hW, hOrbit, e, _, _⟩ := h
  obtain ⟨_, _, _, hs, hclosed, _, _⟩ := MinusculeAndTwoStep.twoStepOrbits
  let hx : IsClosed ({vertex hs} : Set X) := by
    have h : ({vertex hs} : Set X) = Subtype.val ⁻¹' gl2Orbit scalarPair := by
      rw [MinusculeAndTwoStep.twoStepOrbits.2.1]
      ext L
      exact ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩
    rw [h]
    exact hclosed.preimage continuous_subtype_val
  obtain ⟨_, ⟨E, hE, _⟩, _⟩ := MinusculeAndTwoStep.twoStepStableModel
  obtain ⟨P, hP⟩ := LatticeModels.stableSchemePointComparison twoStepBasis twoStepRank shift
  have hP' (q : Points twoStepScheme complexAlgebra) :
      (P q).val = q ≫ twoStepSchemeInGrassmannian := hP q
  have hp' : P p = E (vertex hs) := by
    apply Subtype.ext
    apply grassmannianSubspace_injective twoStepBasis twoStepRank
    rw [hE]
    exact (congrArg (grassmannianSubspace twoStepBasis twoStepRank) (hP p)).trans hp.2.1
  have hU (L : Colength 2) : L ∈ U (vertex hs) hx ↔ L.val ∈ gl2Orbit twoStepPair := by
    rw [MinusculeAndTwoStep.twoStepOrbits.2.2.1]
    exact ⟨fun h ↦ ⟨L.property, fun hn ↦ h (Subtype.ext hn)⟩,
      fun h hn ↦ h.2 (congrArg Subtype.val hn)⟩
  refine ⟨hs, hx, E, P, p, W, hp, hW, ?_, hP, hp', fun L ↦ ⟨hE L, ?_, hU L⟩⟩
  · let j := openOverInclusion W
    let Y := pullback terminalProjection j
    let m : Y ⟶ incidenceScheme := pullback.fst terminalProjection j
    let V := Over.forget (Spec (CommRingCat.of ℂ))
    have hi : IsPullback m.left (pullback.snd terminalProjection j).left terminalProjection.left j.left :=
      (IsPullback.of_hasPullback terminalProjection j).map V
    letI : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion W.ι)
    letI : IsOpenImmersion m.left :=
      MorphismProperty.of_isPullback (P := @IsOpenImmersion) hi.flip inferInstance
    letI : SmoothOfRelativeDimension 0 m.left := inferInstance
    letI : SmoothOfRelativeDimension 2 incidenceScheme.hom := incidenceDimension
    let a : (openOver W).left ≅ Y.left := V.mapIso e.symm
    have hh : (openOver W).hom = a.hom ≫ m.left ≫ incidenceScheme.hom := by
      rw [Over.w]
      exact (Over.w e.inv).symm
    rw [hh, MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 2)]
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 2) (m.left ≫ incidenceScheme.hom))
  · have hcoords : secondPlane (P.symm (E L)) =
        (latticeSubspace 0 2 L.val).map twoStepCoordinates.toLinearMap := by
      unfold secondPlane
      have hq := hP' (P.symm (E L))
      rw [P.apply_symm_apply] at hq
      rw [← hq]
      exact hE L
    exact (hOrbit _ L hcoords).trans (hU L).symm

end Geometry

theorem smoothOpenOrbit_conditional
    (_ : ConvolutionSurfaceSpecs.ExceptionalFibre)
    (_ : ConvolutionSurfaceSpecs.ExceptionalNormalBundle)
    (hOpen : ConvolutionSurfaceSpecs.OpenOrbitIsomorphism)
    (_ : ConvolutionSurfaceSpecs.SurfaceIdentification)
    (_ : TwoStepLocalCohomologySpecs.Expected.JetProductCohomology)
    (_ : TwoStepLocalCohomologySpecs.Expected.RadialNeighborhoodBasis)
    (_ : TwoStepLocalCohomologySpecs.Expected.RadialSheafCohomology)
    (_ : TwoStepLocalCohomologySpecs.Expected.RadialSingularCohomology) :
    TwoStepIntersectionComplexSpecs.Expected.SmoothOpenOrbit := by
  exact smoothFromOpenOrbit hOpen

theorem perverse_conditional
    (_ : ConvolutionSurfaceSpecs.ExceptionalFibre)
    (_ : ConvolutionSurfaceSpecs.ExceptionalNormalBundle)
    (_ : ConvolutionSurfaceSpecs.OpenOrbitIsomorphism)
    (_ : ConvolutionSurfaceSpecs.SurfaceIdentification)
    (_ : TwoStepLocalCohomologySpecs.Expected.JetProductCohomology)
    (hBasis : TwoStepLocalCohomologySpecs.Expected.RadialNeighborhoodBasis)
    (hSheaf : TwoStepLocalCohomologySpecs.Expected.RadialSheafCohomology)
    (hSingular : TwoStepLocalCohomologySpecs.Expected.RadialSingularCohomology) :
    TwoStepIntersectionComplexSpecs.Expected.Perverse := by
  intro h hx
  let x := vertex h
  let a := DerivedLocalSheaves.derivedInverseDirectAdjunctionData (inclusion x hx)
  have hc := shiftedVertexCostalk h hx hBasis hSheaf hSingular
  obtain ⟨e, _, _⟩ := identifySurface x hx hc a
  exact ⟨perverseOfNormalized x hx _ (Iso.refl _) hc,
    perverseOfNormalized x hx _ e.symm hc, shiftedStrict x hx hc, (strictSurface x hx).1⟩

theorem vertexCohomology_conditional
    (_ : ConvolutionSurfaceSpecs.ExceptionalFibre)
    (_ : ConvolutionSurfaceSpecs.ExceptionalNormalBundle)
    (_ : ConvolutionSurfaceSpecs.OpenOrbitIsomorphism)
    (_ : ConvolutionSurfaceSpecs.SurfaceIdentification)
    (_ : TwoStepLocalCohomologySpecs.Expected.JetProductCohomology)
    (hBasis : TwoStepLocalCohomologySpecs.Expected.RadialNeighborhoodBasis)
    (hSheaf : TwoStepLocalCohomologySpecs.Expected.RadialSheafCohomology)
    (hSingular : TwoStepLocalCohomologySpecs.Expected.RadialSingularCohomology) :
    TwoStepIntersectionComplexSpecs.Expected.VertexCohomology := by
  intro h hx
  let x := vertex h
  let a := DerivedLocalSheaves.derivedInverseDirectAdjunctionData (inclusion x hx)
  have hs := shiftedVertexStalk x
  have hc := shiftedVertexCostalk h hx hBasis hSheaf hSingular
  obtain ⟨e, _, _⟩ := identifySurface x hx hc a
  let A := TopCat.of ({x} : Set X)
  let z : A := ⟨x, rfl⟩
  let s (q : ℤ) := (DerivedCategory.Plus.homologyFunctor (Sheaves X) q ⋙ stalk x).mapIso e
  let c (q : ℤ) := (DerivedCategory.Plus.homologyFunctor (Sheaves A) q ⋙ stalk z).mapIso
    ((derivedExtraordinaryInverseImage hx).mapIso e)
  exact ⟨singleDegreeOfIso s hs, singleDegreeOfIso c hc, hs, hc⟩

theorem constantIdentification_conditional
    (_ : ConvolutionSurfaceSpecs.ExceptionalFibre)
    (_ : ConvolutionSurfaceSpecs.ExceptionalNormalBundle)
    (_ : ConvolutionSurfaceSpecs.OpenOrbitIsomorphism)
    (_ : ConvolutionSurfaceSpecs.SurfaceIdentification)
    (_ : TwoStepLocalCohomologySpecs.Expected.JetProductCohomology)
    (hBasis : TwoStepLocalCohomologySpecs.Expected.RadialNeighborhoodBasis)
    (hSheaf : TwoStepLocalCohomologySpecs.Expected.RadialSheafCohomology)
    (hSingular : TwoStepLocalCohomologySpecs.Expected.RadialSingularCohomology) :
    TwoStepIntersectionComplexSpecs.Expected.ConstantIdentification := by
  intro h hx
  dsimp only
  intro a
  exact identifySurface (vertex h) hx (shiftedVertexCostalk h hx hBasis hSheaf hSingular) a

end RepTheorySurvey.Geometric.TwoStepIntersectionComplex

theorem _root_.«RepTheorySurvey».«Geometric».«TwoStepIntersectionComplex».«constantIdentification» : _root_.«RepTheorySurvey».«Geometric».«TwoStepIntersectionComplexSpecs».«Expected».«ConstantIdentification» :=
  @_root_.«RepTheorySurvey».«Geometric».«TwoStepIntersectionComplex».«constantIdentification_conditional» (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«exceptionalFibre») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«exceptionalNormalBundle») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«openOrbitIsomorphism») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«surfaceIdentification») (@_root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«jetProductCohomology») (@_root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«radialNeighborhoodBasis») (@_root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«radialSheafCohomology») (@_root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«radialSingularCohomology»)
theorem _root_.«RepTheorySurvey».«Geometric».«TwoStepIntersectionComplex».«perverse» : _root_.«RepTheorySurvey».«Geometric».«TwoStepIntersectionComplexSpecs».«Expected».«Perverse» :=
  @_root_.«RepTheorySurvey».«Geometric».«TwoStepIntersectionComplex».«perverse_conditional» (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«exceptionalFibre») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«exceptionalNormalBundle») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«openOrbitIsomorphism») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«surfaceIdentification») (@_root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«jetProductCohomology») (@_root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«radialNeighborhoodBasis») (@_root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«radialSheafCohomology») (@_root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«radialSingularCohomology»)
theorem _root_.«RepTheorySurvey».«Geometric».«TwoStepIntersectionComplex».«smoothOpenOrbit» : _root_.«RepTheorySurvey».«Geometric».«TwoStepIntersectionComplexSpecs».«Expected».«SmoothOpenOrbit» :=
  @_root_.«RepTheorySurvey».«Geometric».«TwoStepIntersectionComplex».«smoothOpenOrbit_conditional» (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«exceptionalFibre») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«exceptionalNormalBundle») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«openOrbitIsomorphism») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«surfaceIdentification») (@_root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«jetProductCohomology») (@_root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«radialNeighborhoodBasis») (@_root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«radialSheafCohomology») (@_root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«radialSingularCohomology»)
theorem _root_.«RepTheorySurvey».«Geometric».«TwoStepIntersectionComplex».«vertexCohomology» : _root_.«RepTheorySurvey».«Geometric».«TwoStepIntersectionComplexSpecs».«Expected».«VertexCohomology» :=
  @_root_.«RepTheorySurvey».«Geometric».«TwoStepIntersectionComplex».«vertexCohomology_conditional» (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«exceptionalFibre») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«exceptionalNormalBundle») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«openOrbitIsomorphism») (@_root_.«RepTheorySurvey».«Geometric».«ConvolutionSurface».«surfaceIdentification») (@_root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«jetProductCohomology») (@_root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«radialNeighborhoodBasis») (@_root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«radialSheafCohomology») (@_root_.«RepTheorySurvey».«Geometric».«TwoStepLocalCohomology».«radialSingularCohomology»)
