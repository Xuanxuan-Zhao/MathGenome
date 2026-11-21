import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.RealAnalyticLocal

/-! Independent specification of paper.tex, d13:06:real-analytic.
The real coordinate series, original parameter field, canonical maximal
solution and its actual domain are the shared objects from the local bridge.
This statement includes all terminal/starting-time, state and parameter
variables, arbitrary finite dimensions, and every allowed elapsed time. -/
noncomputable section
namespace Specs.D13Unified.Ch06.RealAnalytic
open Set
open _root_.D13Unified.Ch06.RealAnalytic

/-- The full original corollary. The only regularity hypothesis is joint
real analyticity of the field on its original open domain. -/
def realAnalyticDependence_type : Prop :=
  ∀ (n m : ℕ) (F : _root_.D13Unified.ParameterODE (Fin n → ℝ) (Fin m → ℝ)),
    CoordinateRealAnalyticOn (fieldData ⁻¹' F.domain) (fieldInCoordinates F) →
    IsOpen (solutionDomainInCoordinates F) ∧
      CoordinateRealAnalyticOn (solutionDomainInCoordinates F) (solutionInCoordinates F)

end Specs.D13Unified.Ch06.RealAnalytic
