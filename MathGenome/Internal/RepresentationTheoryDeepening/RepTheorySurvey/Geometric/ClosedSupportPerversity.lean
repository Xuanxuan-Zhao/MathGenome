import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ClosedSupportPerversity
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ClosedSupportBaseChange
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedLocalSheaves
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedSupportBaseChange
noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace
open scoped ZeroObject

namespace RepTheorySurvey.Geometric.ClosedSupportPerversity

open Analytic LocalSheaf
open Analytic.IntersectionComplex (directImageComparison)
open ClosedSupportPerversitySpecs.Expected (ClosedExtensionPerverse)
open ClosedEquivarianceExtensionSpecs (DerivedAdjunctions)

open ClosedSupportBaseChangeSpecs.Expected (ActionProjectionMatesAreIso ClosedBaseChange
  DerivedDirectImageMateEquationIff MateEquationIff StageDatum SupportedRestrictionBijective)

open private derivedClosedImage_supported derivedClosedImageCounit_isIso pullback_supported
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes

open DerivedLocalSheaves (derivedInverseDirectAdjunctionData derivedExtraordinaryAdjunctionData)
open private derivedIsZero pullbackStalkIso pullbackCohomologyIso cohomologyOfFactorIso
  cohomologyIsZero_pullback_iff cohomologyIsZero_iso_iff closedShriekOpenIso
  stratumShriekCohomologyLocality stratumEmbedding shriekOfDisjointSupportZero
  locallyConstantFiniteRank_of_iso pullback_locallyConstantFiniteRank zero_locallyConstantFiniteRank
  embeddingIsoOfRange embeddingIsoOfRange_comp pullbackEquivalence
  derivedDirectImageComposition derivedClosedDirectIso
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

private theorem pullbackIsZeroOfDisjoint {X Y : TopCat.{0}} {S : Set X} {G : BoundedBelow X}
    (g : Y ⟶ X) (hG : DerivedSupportedOn S G) (h : Disjoint (Set.range g) S) :
    IsZero ((boundedBelowInverseImage g).obj G) := by
  apply derivedIsZero
  intro q
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
  intro y
  exact (hG q (g y) (fun hy => Set.disjoint_left.mp h (Set.mem_range_self y) hy)).of_iso
    (pullbackStalkIso g G q y)

private theorem closedImageFiniteCohomology {X Y : TopCat.{0}} {j : Y ⟶ X}
    (hj : IsClosedEmbedding j) (a : DerivedAdjunctions.{0}) (F : BoundedBelow Y)
    (hF : Set.Finite {n : ℤ | ¬ IsZero ((cohomology Y n).obj F.obj)}) :
    Set.Finite {n : ℤ | ¬ IsZero ((cohomology X n).obj ((derivedDirectImage j).obj F).obj)} := by
  let G := (derivedDirectImage j).obj F
  haveI := derivedClosedImageCounit_isIso hj (a j) F
  let c := asIso ((a j).counit.app F)
  refine hF.subset ?_
  intro q hq h
  apply hq
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
  intro x
  by_cases hx : x ∈ Set.range j
  · obtain ⟨y, rfl⟩ := hx
    let e := (stalk y).mapIso ((DerivedCategory.Plus.homologyFunctor _ q).mapIso c)
    exact (((stalk y).map_isZero h).of_iso e).of_iso (pullbackStalkIso j G q y).symm
  · exact derivedClosedImage_supported hj F q x hx

/-- On the range of a closed embedding, the extraordinary inverse image
of its direct image is computed on the inverse image of the closed set. -/
private def shriekClosedImageIso {X Y : TopCat.{0}} {Z : Set X} {V : Set Y}
    (hZ : IsClosed Z) (hV : IsClosed V) {j : Y ⟶ X} (hj : IsClosedEmbedding j)
    (e : TopCat.of Z ≅ TopCat.of V)
    (he : e.hom ≫ closedInclusion V ≫ j = closedInclusion Z) (F : BoundedBelow Y) :
    (derivedExtraordinaryInverseImage hZ).obj ((derivedDirectImage j).obj F) ≅
      (boundedBelowInverseImage e.hom).obj ((derivedExtraordinaryInverseImage hV).obj F) := by
  let E := pullbackEquivalence e
  let a := derivedInverseDirectAdjunctionData j
  let L := boundedBelowInverseImage j
  let A := closedExtensionPlus hZ
  let B := closedExtensionPlus hV
  let d := derivedDirectImage j
  let m := closedInclusion V
  haveI (G : BoundedBelow Y) : IsIso (a.counit.app G) := derivedClosedImageCounit_isIso hj a G
  haveI : IsIso a.counit := NatIso.isIso_of_isIso_app _
  let ε : d ⋙ L ≅ 𝟭 (BoundedBelow Y) := asIso a.counit
  let e₀ : derivedDirectImage e.hom ≅ E.inverse :=
    (derivedInverseDirectAdjunctionData e.hom).rightAdjointUniq E.toAdjunction
  let e₁ : A ≅ E.inverse ⋙ (B ⋙ d) :=
    (derivedClosedDirectIso hZ).symm ≪≫
    eqToIso (congrArg (fun f => derivedDirectImage f) he.symm) ≪≫
    derivedDirectImageComposition e.hom (m ≫ j) ≪≫
    Functor.isoWhiskerLeft _ (derivedDirectImageComposition m j) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (derivedClosedDirectIso hV) _) ≪≫
    Functor.isoWhiskerRight e₀ _
  -- The counit cancels the derived direct image followed by restriction.
  let e₂ : A ⋙ L ≅ E.inverse ⋙ B :=
    Functor.isoWhiskerRight e₁ _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ ε ≪≫ Functor.rightUnitor _)
  let l := ((derivedExtraordinaryAdjunctionData hZ).comp a).ofNatIsoLeft e₂
  let r := E.symm.toAdjunction.comp (derivedExtraordinaryAdjunctionData hV)
  exact (l.rightAdjointUniq r).app F

private def closedStratum {X : TopCat.{0}} {Z : Set X} (hZ : IsClosed Z)
    (d : ℕ) : Stratum X where
  ambientOpen := ⊤
  subset := (openInclusion (⊤ : Opens X)) ⁻¹' Z
  closed := hZ.preimage (openInclusion (⊤ : Opens X)).hom.continuous
  complexDimension := d

private theorem closedStratum_range {X : TopCat.{0}} {Z : Set X} (hZ : IsClosed Z) (d : ℕ) :
    Set.range (closedStratum hZ d).inclusion = Z := by
  ext x
  constructor
  · rintro ⟨⟨⟨y, _⟩, hZy⟩, h⟩
    change y = x at h
    exact h ▸ hZy
  · intro hx
    exact ⟨⟨⟨x, trivial⟩, hx⟩, rfl⟩

private theorem closedStratum_shriek {X : TopCat.{0}} {Z : Set X} (hZ : IsClosed Z) (d : ℕ)
    (F : BoundedBelow X) (q : ℤ) :
    IsZero ((cohomology (TopCat.of Z) q).obj ((derivedExtraordinaryInverseImage hZ).obj F).obj) ↔
      IsZero ((cohomology (closedStratum hZ d).space q).obj
        (((closedStratum hZ d).shriek).obj F).obj) := by
  let S := closedStratum hZ d
  let e := embeddingIsoOfRange (closedInclusion Z) S.inclusion IsEmbedding.subtypeVal
    (stratumEmbedding S) (Subtype.range_coe.trans (closedStratum_range hZ d).symm)
  have he : e.hom ≫ S.inclusion = closedInclusion Z := embeddingIsoOfRange_comp _ _ _ _ _
  let c := closedShriekOpenIso hZ S.closed (openInclusion S.ambientOpen)
    S.ambientOpen.isOpenEmbedding e he F
  exact (cohomologyIsZero_iso_iff c q).trans (cohomologyIsZero_pullback_iff e _ q)

private def openPullback {X Y : TopCat.{0}} (j : Y ⟶ X) (V : Opens X) :
    TopCat.of ((Opens.map j).obj V) ⟶ TopCat.of V :=
  TopCat.ofHom ⟨fun y => ⟨j y.val, y.property⟩,
    (j.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

private theorem openPullback_range {X Y : TopCat.{0}} (j : Y ⟶ X) (V : Opens X) :
    Set.range (openPullback j V) = (openInclusion V) ⁻¹' Set.range j := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.val, rfl⟩
  · rintro ⟨y, h⟩
    have hy : j y ∈ V := h.symm ▸ x.property
    exact ⟨⟨y, hy⟩, Subtype.ext h⟩

private theorem openPullback_closed {X Y : TopCat.{0}} {j : Y ⟶ X} (hj : IsClosedEmbedding j)
    (V : Opens X) : IsClosedEmbedding (openPullback j V) := by
  refine ⟨V.isOpenEmbedding.isEmbedding.of_comp_iff.mp ?_, ?_⟩
  · exact hj.isEmbedding.comp ((Opens.map j).obj V).isOpenEmbedding.isEmbedding
  · rw [openPullback_range]
    exact hj.isClosed_range.preimage (openInclusion V).hom.continuous

private theorem shriekVanishesOnMatchedStratum {X Y : TopCat.{0}} {j : Y ⟶ X}
    (closedBaseChange : ClosedBaseChange)
    (hj : IsClosedEmbedding j) (a : DerivedAdjunctions.{0}) (S : Stratum X) (T : Stratum Y)
    (h : Set.range S.inclusion = j '' Set.range T.inclusion) (F : BoundedBelow Y) (q : ℤ) :
    IsZero ((cohomology T.space q).obj (T.shriek.obj F).obj) →
      IsZero ((cohomology S.space q).obj (S.shriek.obj ((derivedDirectImage j).obj F)).obj) := by
  intro hz
  let O := (Opens.map j).obj S.ambientOpen
  let g := openPullback j S.ambientOpen
  let io := openInclusion O
  let jo := openInclusion S.ambientOpen
  let W := g ⁻¹' S.subset
  let k := closedInclusion W
  have hW : IsClosed W := S.closed.preimage g.hom.continuous
  have hg := openPullback_closed hj S.ambientOpen
  have hrS : Set.range (k ≫ g) = S.subset := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      have hmem : jo x ∈ Set.range S.inclusion := ⟨⟨x, hx⟩, rfl⟩
      rw [h] at hmem
      obtain ⟨y, _, hy⟩ := hmem
      have hy' : y ∈ O := by
        change j y ∈ S.ambientOpen
        exact hy.symm ▸ x.property
      let y' : O := ⟨y, hy'⟩
      have hp : g y' = x := Subtype.ext hy
      exact ⟨⟨y', show g y' ∈ S.subset from hp.symm ▸ hx⟩, hp⟩
  let m : S.space ⟶ TopCat.of S.ambientOpen :=
    closedInclusion (X := TopCat.of S.ambientOpen) S.subset
  let e := embeddingIsoOfRange m (k ≫ g) IsEmbedding.subtypeVal
    (hg.isEmbedding.comp IsEmbedding.subtypeVal) (Subtype.range_coe.trans hrS.symm)
  have he : e.hom ≫ k ≫ g = m := embeddingIsoOfRange_comp m (k ≫ g) _ _ _
  -- Present the source stratum inside the preimage of the ambient open.
  let T' := closedStratum hW T.complexDimension
  have hT' : Set.range T.inclusion = io '' Set.range T'.inclusion := by
    rw [closedStratum_range]
    ext y
    constructor
    · intro hy
      have hx : j y ∈ Set.range S.inclusion := h.symm ▸ Set.mem_image_of_mem j hy
      obtain ⟨⟨x, hx⟩, hxy⟩ := hx
      have hyo : y ∈ O := by
        change j y ∈ S.ambientOpen
        exact hxy ▸ x.property
      let y' : O := ⟨y, hyo⟩
      have hp : g y' = x := Subtype.ext hxy.symm
      exact ⟨y', show g y' ∈ S.subset from hp.symm ▸ hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      have hx : j (io y) ∈ Set.range S.inclusion := ⟨⟨g y, hy⟩, rfl⟩
      rw [h] at hx
      obtain ⟨z, hz, hzy⟩ := hx
      exact hj.isEmbedding.injective hzy ▸ hz
  let F' := (boundedBelowInverseImage io).obj F
  have hm := (stratumShriekCohomologyLocality io O.isOpenEmbedding T T' hT' F q).mp hz
  have hw := (closedStratum_shriek hW T.complexDimension F' q).mpr hm
  have hl := (cohomologyIsZero_pullback_iff e _ q).mpr hw
  letI := closedBaseChange hj hg (show g ≫ jo = io ≫ j from rfl)
    (openPullback_range j S.ambientOpen) a F
  let c := asIso (directImageComparison (show g ≫ jo = io ≫ j from rfl) (a g) (a j) F)
  let d := (derivedExtraordinaryInverseImage S.closed).mapIso c ≪≫
    shriekClosedImageIso S.closed hW hg e he F'
  exact (cohomologyIsZero_iso_iff d q).mpr hl

private theorem shriekIsZeroOnDisjointStratum {X Y : TopCat.{0}} {j : Y ⟶ X}
    (hj : IsClosedEmbedding j) (S : Stratum X)
    (h : Disjoint (Set.range S.inclusion) (Set.range j)) (F : BoundedBelow Y) :
    IsZero (S.shriek.obj ((derivedDirectImage j).obj F)) := by
  let V := S.ambientOpen
  let p := openInclusion V
  let G := (boundedBelowInverseImage p).obj ((derivedDirectImage j).obj F)
  let Z := p ⁻¹' Set.range j
  have hZ : IsClosed Z := hj.isClosed_range.preimage p.hom.continuous
  let U : Opens (TopCat.of V) := ⟨Zᶜ, hZ.isOpen_compl⟩
  let k := openInclusion U
  have hr : Set.range k = Zᶜ := Subtype.range_coe
  have hsub : S.subset ⊆ Set.range k := by
    intro z hz
    rw [hr]
    exact fun hq => Set.disjoint_left.mp h ⟨⟨z, hz⟩, rfl⟩ hq
  have hd : Disjoint (Set.range k) Z := by rw [hr]; exact disjoint_compl_left
  have hz := pullbackIsZeroOfDisjoint k (pullback_supported p _ _ (derivedClosedImage_supported hj F)) hd
  exact shriekOfDisjointSupportZero S.closed U.isOpenEmbedding hsub G hz

/-- Closed extension preserves middle perversity on the containing stage.
The conditional premises are given in the order of the closed-support interface. -/
theorem closedExtensionPerverse_conditional
    (_ : ActionProjectionMatesAreIso)
    (closedBaseChange : ClosedBaseChange)
    (_ : DerivedDirectImageMateEquationIff)
    (_ : MateEquationIff)
    (_ : StageDatum)
    (_ : SupportedRestrictionBijective) :
    ClosedExtensionPerverse := by
  intro Y X A P Q n j hj index rangeEq dimensionEq disjoint F hp
  let a := fun {Y X : TopCat.{0}} (m : Y ⟶ X) => derivedInverseDirectAdjunctionData m
  let G := (derivedDirectImage j).obj F
  haveI := derivedClosedImageCounit_isIso hj (a j) F
  let c := asIso ((a j).counit.app F)
  have hG : IsMiddlePerverse (Q n) G.obj := by
    have rangeCase (s : (Q n).Index) :
        (∃ p : P.Index,
          Set.range ((Q n).stratum s).inclusion = j '' Set.range (P.stratum p).inclusion ∧
          ((Q n).stratum s).complexDimension = (P.stratum p).complexDimension) ∨
        Disjoint (Set.range ((Q n).stratum s).inclusion) (Set.range j) := by
      by_cases hs : Set.range ((Q n).stratum s).inclusion ⊆ Set.range j
      · let p := index.symm ⟨s, hs⟩
        have he : (index p).val = s :=
          congrArg Subtype.val (index.apply_symm_apply ⟨s, hs⟩)
        exact .inl ⟨p, he ▸ rangeEq p, he ▸ dimensionEq p⟩
      · exact .inr (disjoint s hs)
    have matchCohom {s : (Q n).Index} {p : P.Index}
        (hr : Set.range ((Q n).stratum s).inclusion = j '' Set.range (P.stratum p).inclusion)
        (q : ℤ) :
        ∃ e : ((Q n).stratum s).space ≅ (P.stratum p).space,
          Nonempty ((inverseImage ((Q n).stratum s).inclusion).obj
            ((cohomology _ q).obj G.obj) ≅ (inverseImage e.hom).obj
              ((inverseImage (P.stratum p).inclusion).obj ((cohomology Y q).obj F.obj))) := by
      let S := (Q n).stratum s
      let T := P.stratum p
      have hr' : Set.range (T.inclusion ≫ j) = Set.range S.inclusion := by
        rw [hr]
        exact Set.range_comp j T.inclusion
      let e := embeddingIsoOfRange S.inclusion (T.inclusion ≫ j) (stratumEmbedding S)
        (hj.isEmbedding.comp (stratumEmbedding T)) hr'.symm
      have he : (e.hom ≫ T.inclusion) ≫ j = S.inclusion := by
        rw [Category.assoc]
        exact embeddingIsoOfRange_comp _ _ _ _ _
      exact ⟨e, ⟨cohomologyOfFactorIso j he G F c q ≪≫
        (inverseImageComposition e.hom T.inclusion).app _⟩⟩
    refine ⟨⟨closedImageFiniteCohomology hj a F hp.1.1, ?_⟩, G.property, ?_⟩
    · intro s q
      rcases rangeCase s with ⟨p, hr, hd⟩ | h
      · obtain ⟨e, ⟨k⟩⟩ := matchCohom hr q
        exact locallyConstantFiniteRank_of_iso k.symm
          (pullback_locallyConstantFiniteRank e.hom (hp.1.2 p q))
      · let m := ((Q n).stratum s).inclusion
        have hzero := pullbackIsZeroOfDisjoint m (derivedClosedImage_supported hj F) h
        let c := pullbackCohomologyIso m G q
        exact zero_locallyConstantFiniteRank
          (((DerivedCategory.Plus.homologyFunctor _ q).map_isZero hzero).of_iso c.symm)
    · intro s
      rcases rangeCase s with ⟨p, hr, hd⟩ | h
      · constructor
        · intro q hq
          obtain ⟨e, ⟨k⟩⟩ := matchCohom hr q
          have hq' : -(P.stratum p).complexDimension < q := by rwa [hd] at hq
          let cP := pullbackCohomologyIso (P.stratum p).inclusion F q
          let cQ := pullbackCohomologyIso ((Q n).stratum s).inclusion G q
          let d := cQ ≪≫ k ≪≫ (inverseImage e.hom).mapIso cP.symm
          exact ((inverseImage e.hom).map_isZero (hp.2.choose_spec p |>.1 q hq')).of_iso d
        · intro q hq
          have hq' : q < -(P.stratum p).complexDimension := by rwa [hd] at hq
          exact shriekVanishesOnMatchedStratum closedBaseChange hj a _ _ hr F q
            (hp.2.choose_spec p |>.2 q hq')
      · constructor
        · intro q _
          exact (DerivedCategory.Plus.homologyFunctor _ q).map_isZero
            (pullbackIsZeroOfDisjoint _ (derivedClosedImage_supported hj F) h)
        · intro q _
          exact (DerivedCategory.Plus.homologyFunctor _ q).map_isZero
            (shriekIsZeroOnDisjointStratum hj _ h F)
  -- Identify the composite image with exact extension from this stage.
  refine ⟨hG, ⟨n, ⟨G.obj, hG⟩, ⟨?_⟩⟩⟩
  let d := (derivedDirectImageComposition j (A.inclusion n)).app F ≪≫
    (derivedClosedDirectIso (A.closed n)).app G
  exact (DerivedCategory.Plus.ι (C := Sheaves X)).mapIso d.symm

end RepTheorySurvey.Geometric.ClosedSupportPerversity

theorem _root_.«RepTheorySurvey».«Geometric».«ClosedSupportPerversity».«closedExtensionPerverse» : _root_.«RepTheorySurvey».«Geometric».«ClosedSupportPerversitySpecs».«Expected».«ClosedExtensionPerverse» :=
  @_root_.«RepTheorySurvey».«Geometric».«ClosedSupportPerversity».«closedExtensionPerverse_conditional» (@_root_.«RepTheorySurvey».«Geometric».«ClosedSupportBaseChange».«actionProjectionMatesAreIso») (@_root_.«RepTheorySurvey».«Geometric».«ClosedSupportBaseChange».«closedBaseChange») (@_root_.«RepTheorySurvey».«Geometric».«ClosedSupportBaseChange».«derivedDirectImageMateEquationIff») (@_root_.«RepTheorySurvey».«Geometric».«ClosedSupportBaseChange».«mateEquationIff») (@_root_.«RepTheorySurvey».«Geometric».«ClosedSupportBaseChange».«stageDatum») (@_root_.«RepTheorySurvey».«Geometric».«ClosedSupportBaseChange».«supportedRestrictionBijective»)
