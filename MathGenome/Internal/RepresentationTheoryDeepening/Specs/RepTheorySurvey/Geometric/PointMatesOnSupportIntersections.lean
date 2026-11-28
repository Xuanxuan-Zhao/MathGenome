import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.FiniteStageClosedExtensions
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ClosedSupportBaseChange

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace RepTheorySurvey.Geometric.PointMatesOnSupportIntersectionsSpecs.Expected

open Analytic Analytic.IntersectionComplex LocalSheaf
open ClosedEquivarianceExtensionSpecs (DerivedAdjunctions parameterInclusion projectionSquare)
open ClosedSupportBaseChangeSpecs (MateCommutes)
open EquivariantIntersectionComplexesSpecs (Intertwines)
open FiniteStageClosedExtensionSpecs (SupportIntersections PointIntersectionMaps
  LocalPointCompatibility)

/-- The exact closed-point extension's action and projection mate equation
restricts to the point and surface intersections with each closed stage. -/
def PointMatesOnIntersections : Prop :=
  ∀ {X Y : TopCat.{0}} {J : JetSystem.{0}} {A : ClosedStages X}
    {B : StageJetActions J A} {i : Y ⟶ X} {x : Y}
    {S : JetAction J Y} {T : JetAction J (TopCat.of ({x} : Set Y))}
    (hx : IsClosed ({x} : Set Y))
    (D : SupportIntersections B i S)
    (P : SupportIntersections B (closedInclusion ({x} : Set Y) ≫ i) T)
    (I : PointIntersectionMaps D P)
    (hPoint : Intertwines T S (closedInclusion ({x} : Set Y)))
    (a : DerivedAdjunctions.{0})
    (b : boundedBelowInverseImage (closedInclusion ({x} : Set Y)) ⊣ closedExtensionPlus hx)
    {F : BoundedBelow (TopCat.of ({x} : Set Y))}
    {α : T.Equivariance F.obj}
    {γ : S.Equivariance ((closedExtensionPlus hx).obj F).obj}
    (Lₚ : P.LocalEquivariance F α)
    (L : D.LocalEquivariance ((closedExtensionPlus hx).obj F) γ),
    (∀ (k : ℕ) (hₚ : T.cutoff ≤ k) (hₛ : S.cutoff ≤ k),
      let H := J.group k
      let p := closedInclusion ({x} : Set Y)
      MateCommutes (hPoint k hₚ hₛ) (projectionSquare H p)
        (a (parameterInclusion H p)) b (𝟙 ((closedExtensionPlus hx).obj F))
        (γ.datum k hₛ).iso.hom (α.datum k hₚ).iso.hom) →
    (∀ (n k : ℕ), (P.action n).cutoff ≤ k → (D.action n).cutoff ≤ k →
      (T.cutoff ≤ k ∧ S.cutoff ≤ k) ∨ IsEmpty (P.space n)) →
    LocalPointCompatibility D P I hx a b Lₚ L

end RepTheorySurvey.Geometric.PointMatesOnSupportIntersectionsSpecs.Expected
