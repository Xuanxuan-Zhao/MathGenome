import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.RealAnalyticLocal

/-! The long-real-time part of paper.tex, d13:06:real-analytic.
The premise is only a neighborhood of each admissible diagonal datum.
All coordinates and canonical solution choices are those of the local child. -/
noncomputable section
namespace Specs.D13Unified.Ch06.RealAnalyticPropagation
open Set Metric
open _root_.D13Unified _root_.D13Unified.Ch06.RealAnalytic
open Ch03.LocalLipschitz

/-- Local joint real analyticity propagates over the entire actual maximal
domain, in arbitrary finite state and parameter dimensions and both time
directions. No bound on the allowed finite elapsed time is imposed. -/
def realAnalyticPropagation_type : Prop :=
  ∀ {n m : ℕ} (F : ParameterODE (Fin n → ℝ) (Fin m → ℝ)),
    parameterLocallyLipschitzInStateValue F →
    (∀ (s : ℝ) (ξ : Fin n → ℝ) (p : Fin m → ℝ), ((s, ξ), p) ∈ F.domain →
      ∃ r : ℝ, 0 < r ∧
        ball (Fin.cons s (realFieldPoint s ξ p)) r ⊆ solutionDomainInCoordinates F ∧
        CoordinateRealAnalyticOn (ball (Fin.cons s (realFieldPoint s ξ p)) r)
          (solutionInCoordinates F)) →
    CoordinateRealAnalyticOn (solutionDomainInCoordinates F) (solutionInCoordinates F)

end Specs.D13Unified.Ch06.RealAnalyticPropagation
