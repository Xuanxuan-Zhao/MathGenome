import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ClosedSupportBaseChange
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ClosedSupportPullbackPasting
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.FullSupportCounitComparison

noncomputable section

set_option autoImplicit false

open CategoryTheory Topology

namespace RepTheorySurvey.Geometric.ClosedSupportStageCompatibilitySpecs.Expected

open Analytic Analytic.IntersectionComplex
open AnalyticAction (projection)
open ClosedEquivarianceExtensionSpecs (DerivedAdjunctions parameterInclusion projectionSquare)
open ClosedSupportBaseChangeSpecs (AgreesWithMates MateCommutes MatesAreIso)
open ClosedSupportPullbackPastingSpecs (pullbackComparisonAt)
open EquivariantIntersectionComplexesSpecs (Intertwines IntertwinesPullback restrictedArrow)
open FullSupportCounitComparisonSpecs (fullSupportComparison)

/-- At a common jet, the two stage arrows transported by their actual mates
agree under stage restriction and the canonical comparison of inverse images. -/
def StageTransitionCompatibility : Prop :=
  ∀ {X Y U₀ U₁ V₀ V₁ : TopCat.{0}} {i : Y ⟶ X}
    {j₀ : U₀ ⟶ V₀} {j₁ : U₁ ⟶ V₁} {v₀ : U₀ ⟶ Y} {v₁ : U₁ ⟶ Y}
    {t₀ : V₀ ⟶ X} {t₁ : V₁ ⟶ X} {r : U₀ ⟶ U₁} {s : V₀ ⟶ V₁}
    (_hi : IsClosedEmbedding i) (_hj₀ : IsClosedEmbedding j₀)
    (_hj₁ : IsClosedEmbedding j₁)
    (h₀ : j₀ ≫ t₀ = v₀ ≫ i) (h₁ : j₁ ≫ t₁ = v₁ ≫ i)
    (_range₀ : Set.range j₀ = t₀ ⁻¹' Set.range i)
    (_range₁ : Set.range j₁ = t₁ ⁻¹' Set.range i)
    (_hStage : r ≫ j₁ = j₀ ≫ s) (hSupport : r ≫ v₁ = v₀) (hAmbient : s ≫ t₁ = t₀)
    {J : JetSystem.{0}} {C₀ : JetAction J U₀} {C₁ : JetAction J U₁}
    {E₀ : JetAction J V₀} {E₁ : JetAction J V₁}
    (hAct₀ : Intertwines C₀ E₀ j₀) (hAct₁ : Intertwines C₁ E₁ j₁)
    (hLocal : Intertwines C₀ C₁ r)
    (a : DerivedAdjunctions.{0}) (F : BoundedBelow Y)
    (α₀ : C₀.Equivariance ((boundedBelowInverseImage v₀).obj F).obj)
    (α₁ : C₁.Equivariance ((boundedBelowInverseImage v₁).obj F).obj)
    (β₀ : E₀.Equivariance ((boundedBelowInverseImage t₀).obj ((derivedDirectImage i).obj F)).obj)
    (β₁ : E₁.Equivariance ((boundedBelowInverseImage t₁).obj ((derivedDirectImage i).obj F)).obj)
    (k : ℕ) (hc₀ : C₀.cutoff ≤ k) (hc₁ : C₁.cutoff ≤ k)
    (he₀ : E₀.cutoff ≤ k) (he₁ : E₁.cutoff ≤ k)
    (hAction : J.parameterMap (le_refl k) s ≫ (E₁.action k he₁).act =
      (E₀.action k he₀).act ≫ s),
    let H := J.group k
    MateCommutes (hAct₀ k hc₀ he₀) (projectionSquare H j₀)
      (a (parameterInclusion H j₀)) (a j₀) (directImageComparison h₀ (a j₀) (a i) F)
      (β₀.datum k he₀).iso.hom (α₀.datum k hc₀).iso.hom →
    MateCommutes (hAct₁ k hc₁ he₁) (projectionSquare H j₁)
      (a (parameterInclusion H j₁)) (a j₁) (directImageComparison h₁ (a j₁) (a i) F)
      (β₁.datum k he₁).iso.hom (α₁.datum k hc₁).iso.hom →
    let c := (pullbackComparisonAt r v₁ hSupport F).hom.hom
    (derivedInverseImage (C₀.action k hc₀).act).map c ≫ restrictedArrow hLocal α₁ k hc₀ hc₁ =
        (α₀.datum k hc₀).iso.hom ≫ (derivedInverseImage (projection H U₀)).map c →
    let G := ((derivedDirectImage i).obj F).obj
    let G₁ := (derivedInverseImage t₁).obj G
    let e₀ := (E₀.action k he₀).act
    let p₀ := projection H V₀
    let σ := eqToIso (congrArg (fun f => (derivedInverseImage f).obj G) hAmbient.symm) ≪≫
      (derivedInverseImageComposition s t₁).app G
    (derivedInverseImage e₀).map σ.hom ≫
        (derivedInverseImageComposition e₀ s).inv.app G₁ ≫
        pullbackMorphism (J.parameterMap (le_refl k) s) hAction
          (show _ ≫ projection H V₁ = p₀ ≫ s from TopCat.ext (fun _ => rfl))
          (β₁.datum k he₁).iso.hom ≫
        (derivedInverseImageComposition p₀ s).hom.app G₁ ≫
        (derivedInverseImage p₀).map σ.inv =
      (β₀.datum k he₀).iso.hom

/-- On a stage containing the entire support, the realized stage datum agrees
with the support datum via the full-support comparison, with invertible ordinary,
action and projection comparisons. -/
def FullSupportCompatibility : Prop :=
  ∀ {X Y U V : TopCat.{0}} {i : Y ⟶ X} {u : U ⟶ V} {v : U ⟶ Y} {t : V ⟶ X}
    (_hi : IsClosedEmbedding i) (_hu : IsClosedEmbedding u) (_ht : IsClosedEmbedding t)
    (hs : u ≫ t = v ≫ i) (_range : Set.range u = t ⁻¹' Set.range i)
    {J : JetSystem.{0}} {C : JetAction J U} {S : JetAction J Y} {E : JetAction J V}
    (_cutoff : C.cutoff ≤ E.cutoff)
    (hStage : Intertwines C E u) (hSupport : Intertwines C S v)
    (a : DerivedAdjunctions.{0}) (F : BoundedBelow Y)
    (α : S.Equivariance F.obj)
    (γ : C.Equivariance ((boundedBelowInverseImage v).obj F).obj)
    (β : E.Equivariance ((boundedBelowInverseImage t).obj ((derivedDirectImage i).obj F)).obj)
    (_local : IntertwinesPullback hSupport γ α (𝟙 _))
    (_agrees : AgreesWithMates hStage a γ β (directImageComparison hs (a u) (a i) F).hom)
    (j : Y ⟶ V) (h : j ≫ t = i) (hAction : Intertwines S E j),
      let c := (fullSupportComparison h a F).hom
      IsIso c ∧ MatesAreIso hAction a F ∧ AgreesWithMates hAction a α β c

end RepTheorySurvey.Geometric.ClosedSupportStageCompatibilitySpecs.Expected
