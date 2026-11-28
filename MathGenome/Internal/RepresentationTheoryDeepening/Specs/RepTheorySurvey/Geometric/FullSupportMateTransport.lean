import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ClosedSupportBaseChange

noncomputable section

set_option autoImplicit false

open CategoryTheory Topology

namespace RepTheorySurvey.Geometric.FullSupportMateTransportSpecs.Expected

open Analytic Analytic.IntersectionComplex LocalSheaf
open AnalyticAction (projection)
open ClosedEquivarianceExtensionSpecs (DerivedAdjunctions parameterInclusion projectionSquare)
open ClosedSupportBaseChangeSpecs (MateCommutes SquareRestriction)

/-- At a common analytic parameter group, transport the mate equation from the closed
intersection to the full support through a factorization with compatible coefficient
transposes. -/
def FullSupportMateTransport : Prop :=
  ∀ {U Y V : TopCat.{0}} {v : U ⟶ Y} {j : Y ⟶ V} {u : U ⟶ V}
    (factor : v ≫ j = u) (_hu : IsClosedEmbedding u)
    {H : AnalyticGroup.{0}}
    (A_U : AnalyticAction H U) (A_Y : AnalyticAction H Y) (A_V : AnalyticAction H V)
    (hv : parameterInclusion H v ≫ A_Y.act = A_U.act ≫ v)
    (hj : parameterInclusion H j ≫ A_V.act = A_Y.act ≫ j)
    (hu : parameterInclusion H u ≫ A_V.act = A_U.act ≫ u)
    (a : DerivedAdjunctions.{0})
    {G : BoundedBelow V} {F : BoundedBelow Y}
    (c : G ⟶ (derivedDirectImage j).obj F),
    let K := (boundedBelowInverseImage v).obj F
    ∀ (d : G ⟶ (derivedDirectImage u).obj K)
      (_hc : IsIso c) (_hd : IsIso d)
      (_hp : IsIso (directImageComparison (projectionSquare H j)
        (a (parameterInclusion H j)) (a j) F))
      (_support : DerivedSupportedOn (Set.range (parameterInclusion H u))
        ((boundedBelowInverseImage (projection H V)).obj G))
      (α : (derivedInverseImage A_V.act).obj G.obj ⟶
        (derivedInverseImage (projection H V)).obj G.obj)
      (β : (derivedInverseImage A_Y.act).obj F.obj ⟶
        (derivedInverseImage (projection H Y)).obj F.obj)
      (γ : (derivedInverseImage A_U.act).obj K.obj ⟶
        (derivedInverseImage (projection H U)).obj K.obj),
      let εj := ((boundedBelowInverseImage j).map c ≫ (a j).counit.app F).hom
      let εu := ((boundedBelowInverseImage u).map d ≫ (a u).counit.app K).hom
      εu = eqToHom (congrArg (fun f : U ⟶ V => (derivedInverseImage f).obj G.obj) factor.symm) ≫
        (derivedInverseImageComposition v j).hom.app G.obj ≫ (derivedInverseImage v).map εj →
      SquareRestriction hv (projectionSquare H v) (𝟙 K.obj) β γ →
      MateCommutes hu (projectionSquare H u) (a (parameterInclusion H u)) (a u) d α γ →
      MateCommutes hj (projectionSquare H j) (a (parameterInclusion H j)) (a j) c α β

end RepTheorySurvey.Geometric.FullSupportMateTransportSpecs.Expected
