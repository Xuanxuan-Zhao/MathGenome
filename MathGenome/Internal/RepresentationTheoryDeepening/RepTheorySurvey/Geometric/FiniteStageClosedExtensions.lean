import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.FiniteStageClosedExtensions
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedSupportBaseChange
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedSupportPullbackPasting
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedSupportStageCompatibility
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedSupportPerversity
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedPointExtensionComposition
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Topology

namespace RepTheorySurvey.Geometric.FiniteStageClosedExtensions

open Analytic Analytic.IntersectionComplex LocalSheaf
open FiniteStageClosedExtensionSpecs
open ClosedEquivarianceExtensionSpecs (DerivedAdjunctions parameterInclusion projectionSquare)
open ClosedSupportBaseChangeSpecs (MateCommutes)
open EquivariantIntersectionComplexesSpecs (Intertwines)
open private directImageComparisonNaturality from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

theorem closedBaseChange : Expected.ClosedBaseChange :=
  ClosedSupportBaseChange.closedBaseChange

theorem stageComparisonPasting : Expected.StageComparisonPasting := by
  intro X Y J A B i S D a F n m h
  exact ClosedSupportPullbackPasting.mateVerticalPasting (D.square m) (D.transition_stage h).symm
    (A.transition_inclusion h) (D.transition_support h) (D.square n)
    (a i) (a (D.intoStage m)) (a (D.intoStage n)) F

private theorem mateCommutesAtLevel {U V : TopCat.{0}} {J : JetSystem.{0}}
    {C : JetAction J U} {E : JetAction J V} {j : U ⟶ V}
    (h : Intertwines C E j) (a : DerivedAdjunctions.{0})
    {F : BoundedBelow U} {G : BoundedBelow V} (c : G ⟶ (derivedDirectImage j).obj F)
    {α : C.Equivariance F.obj} {β : E.Equivariance G.obj}
    (hβ : AgreesWithMates h a α β c.hom) (k : ℕ) (hu : C.cutoff ≤ k) (hv : E.cutoff ≤ k) :
    MateCommutes (h k hu hv) (projectionSquare (J.group k) j)
      (a (parameterInclusion (J.group k) j)) (a j) c
      (β.datum k hv).iso.hom (α.datum k hu).iso.hom := by
  simp only [MateCommutes, ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
  exact hβ k hu hv

theorem closedExtensionAtStages : Expected.ClosedExtensionAtStages := by
  intro X Y J A B i S hi D a F α L
  have lift (n : ℕ) := ClosedSupportBaseChange.stageDatum hi (D.closed n) (D.square n)
    (D.range_eq n) (D.stageActionSquare n) (D.cutoff_le n) a F (L.datum n)
  choose β hβ using lift
  let global : B.Equivariance ((derivedDirectImage i).obj F).obj :=
    { datum := β
      compatibility := by
        intro n m k h hn hm
        let un := (D.cutoff_le n).trans hn
        let um := (D.cutoff_le m).trans hm
        exact ClosedSupportStageCompatibility.stageTransitionCompatibility
          hi (D.closed n) (D.closed m) (D.square n) (D.square m)
          (D.range_eq n) (D.range_eq m) (D.transition_stage h) (D.transition_support h)
          (A.transition_inclusion h) (D.stageActionSquare n) (D.stageActionSquare m)
          (D.transitionActionSquare h) a F (L.datum n) (L.datum m) (β n) (β m)
          k un um hn hm (B.compatible h hn hm)
          (mateCommutesAtLevel (D.stageActionSquare n) a (D.stageComparison a F n)
            (hβ n).2.2 k un hn)
          (mateCommutesAtLevel (D.stageActionSquare m) a (D.stageComparison a F m)
            (hβ m).2.2 k um hm)
          (L.onTransitions h k un um) }
  refine ⟨global, hβ, ?_⟩
  intro n j h commutes
  exact ClosedSupportStageCompatibility.fullSupportCompatibility hi (D.closed n)
    (A.closed n).isClosedEmbedding_subtypeVal (D.square n) (D.range_eq n)
    (D.cutoff_le n) (D.stageActionSquare n) (D.supportActionSquare n)
    a F α (L.datum n) (β n) (L.onSupport n) (hβ n).2.2 j h commutes

private theorem commutesOfComparisons {K : Type*} [Category K]
    {X₁ X₂ Y₁ Y₂ U₁ U₂ V₁ V₂ : K}
    {a : X₁ ⟶ X₂} {p : Y₁ ⟶ Y₂} {v : U₁ ⟶ U₂} {w : V₁ ⟶ V₂}
    {α : X₁ ⟶ Y₁} {β : X₂ ⟶ Y₂} {γ : U₁ ⟶ V₁} {δ : U₂ ⟶ V₂}
    {c₁ : X₁ ⟶ U₁} {c₂ : X₂ ⟶ U₂} {d₁ : Y₁ ⟶ V₁} {d₂ : Y₂ ⟶ V₂}
    [Mono d₂] (ha : a ≫ c₂ = c₁ ≫ v) (hp : p ≫ d₂ = d₁ ≫ w)
    (hα : α ≫ d₁ = c₁ ≫ γ) (hβ : β ≫ d₂ = c₂ ≫ δ) (hγ : v ≫ δ = γ ≫ w) :
    a ≫ β = α ≫ p := by
  apply (cancel_mono d₂).mp
  simp only [Category.assoc]
  rw [hβ, ← Category.assoc a, ha, Category.assoc, hγ, hp, ← Category.assoc α, hα,
    Category.assoc]

theorem closedExtensionNaturality : Expected.ClosedExtensionNaturality := by
  intro X Y J A B i S D a F G f
  have hnat (n : ℕ) := directImageComparisonNaturality (D.square n) (a (D.intoStage n)) (a i) f
  refine ⟨hnat, ?_⟩
  intro α γ L M β δ hb hd hf
  refine ⟨⟨((derivedDirectImage i).map f).hom, ?_⟩, rfl⟩
  intro n k hk
  let hu := (D.cutoff_le n).trans hk
  let H := J.group k
  let j := D.intoStage n
  let jH := parameterInclusion H j
  let q := (boundedBelowInverseImage (D.intoSupport n)).map f
  let m := (boundedBelowInverseImage (A.inclusion n)).map ((derivedDirectImage i).map f)
  let cF := D.stageComparison a F n
  let cG := D.stageComparison a G n
  let hA := D.stageActionSquare n k hu hk
  let hP := projectionSquare H j
  have hca := ClosedSupportPullbackPasting.mateNaturality hA (a jH) (a j) q m cF cG (hnat n)
  have hcp := ClosedSupportPullbackPasting.mateNaturality hP (a jH) (a j) q m cF cG (hnat n)
  let bA := ((D.action n).action k hu).act
  let bP := AnalyticAction.projection H (D.space n)
  let bF : (boundedBelowInverseImage bA).obj (D.intersectionRestriction F n) ⟶
      (boundedBelowInverseImage bP).obj (D.intersectionRestriction F n) :=
    ObjectProperty.homMk ((L.datum n).datum k hu).iso.hom
  let bG : (boundedBelowInverseImage bA).obj (D.intersectionRestriction G n) ⟶
      (boundedBelowInverseImage bP).obj (D.intersectionRestriction G n) :=
    ObjectProperty.homMk ((M.datum n).datum k hu).iso.hom
  have hq : (boundedBelowInverseImage bA).map q ≫ bG =
      bF ≫ (boundedBelowInverseImage bP).map q := ObjectProperty.hom_ext _ (hf n k hu)
  have hqm := congrArg (fun f => ((derivedDirectImage jH).map f).hom) hq
  simp only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom] at hqm
  let gP := (boundedBelowInverseImage (AnalyticAction.projection H (A.space n))).map cG ≫
      directImageComparison hP (a jH) (a j) (D.intersectionRestriction G n)
  let fP := (boundedBelowInverseImage (AnalyticAction.projection H (A.space n))).map cF ≫
      directImageComparison hP (a jH) (a j) (D.intersectionRestriction F n)
  let gA := (boundedBelowInverseImage ((B.stageAction n).action k hk).act).map cG ≫
      directImageComparison hA (a jH) (a j) (D.intersectionRestriction G n)
  let fA := (boundedBelowInverseImage ((B.stageAction n).action k hk).act).map cF ≫
      directImageComparison hA (a jH) (a j) (D.intersectionRestriction F n)
  haveI : IsIso cG := (hd n).1
  haveI : IsIso (directImageComparison hP (a jH) (a j) (D.intersectionRestriction G n)) :=
    ((hd n).2.1 k hu hk).2
  haveI : IsIso gP := by dsimp only [gP]; infer_instance
  let d := DerivedCategory.Plus.ι (C := Sheaves (AnalyticAction.Parameters H (A.space n)))
  haveI : IsIso gP.hom := d.map_isIso gP
  have hF : ((β.datum n).datum k hk).iso.hom ≫ fP.hom =
      fA.hom ≫ ((derivedDirectImage jH).map bF).hom := by
    simpa only [fP, fA, cF, bF, ObjectProperty.FullSubcategory.comp_hom, Category.assoc] using!
      ((hb n).2.2 k hu hk)
  have hG : ((δ.datum n).datum k hk).iso.hom ≫ gP.hom =
      gA.hom ≫ ((derivedDirectImage jH).map bG).hom := by
    simpa only [gP, gA, cG, bG, ObjectProperty.FullSubcategory.comp_hom, Category.assoc] using!
      ((hd n).2.2 k hu hk)
  exact commutesOfComparisons (d₂ := gP.hom)
    (congrArg d.map hca) (congrArg d.map hcp) hF hG hqm


theorem closedExtensionPerverse : Expected.ClosedExtensionPerverse := by
  intro Y X A P Q n j hj hStrata F hF
  exact ClosedSupportPerversity.closedExtensionPerverse A P Q n j hj
    hStrata.index hStrata.range_eq hStrata.dimension_eq hStrata.disjoint F hF

theorem closedPointCompositionEquivariant : Expected.ClosedPointCompositionEquivariant := by
  intro X Y J A B i x S T hi hx D P I a b F α γ Lₚ L β δ hβ hδ hPoint
  refine ⟨⟨((closedPointComposition hx i a b).hom.app F).hom, ?_⟩, rfl⟩
  intro n k hk
  let hu := (P.cutoff_le n).trans hk
  let hv := (D.cutoff_le n).trans hk
  exact ClosedPointExtensionComposition.closedPointCompositionEquivariant hx hi
    (D.closed n) (P.closed n) (D.square n) (D.range_eq n) (P.square n) (P.range_eq n)
    (I.stage n) (I.support n)
    ((B.stageAction n).action k hk) ((D.action n).action k hv) ((P.action n).action k hu)
    (D.stageActionSquare n k hv hk) (P.stageActionSquare n k hu hk) (I.actionSquare n k hu hv)
    a b F ((β.datum n).datum k hk).iso.hom ((δ.datum n).datum k hk).iso.hom
    ((L.datum n).datum k hv).iso.hom ((Lₚ.datum n).datum k hu).iso.hom
    (mateCommutesAtLevel (P.stageActionSquare n) a (P.stageComparison a F n)
      (hβ n).2.2 k hu hk)
    (mateCommutesAtLevel (D.stageActionSquare n) a (D.stageComparison a ((closedExtensionPlus hx).obj F) n)
      (hδ n).2.2 k hv hk)
    (mateCommutesAtLevel (I.actionSquare n) a
      (adjointSquareMap (pullbackSquare (I.support n)) (a (I.inclusion n)) b F)
      (hPoint n) k hu hv)

end RepTheorySurvey.Geometric.FiniteStageClosedExtensions
