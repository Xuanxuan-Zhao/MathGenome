import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch09.SmoothedCdfDifferenceInversion

open MeasureTheory Set

namespace Specs.ProbabilityFoundations.Ch09.EsseenSmoothingInequality

/-- The same positive real constant works for every pair of laws, every
Lipschitz constant and every positive cutoff. The integrand is set to zero
at zero by real division; no equality of the first moments is assumed. -/
def SmoothingInequality : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      Integrable (fun x : ℝ => |x|) μ → Integrable (fun x : ℝ => |x|) ν →
      ∀ M : ℝ, 0 ≤ M →
      (∀ x y : ℝ,
        |Ch01.RealDistributionFunctions.distributionFunctionValue ν x -
          Ch01.RealDistributionFunctions.distributionFunctionValue ν y| ≤ M * |x - y|) →
      ∀ T : ℝ, 0 < T →
        IntegrableOn (fun t : ℝ => ‖charFun μ t - charFun ν t‖ / |t|) (Icc (-T) T) ∧
        (⨆ x : ℝ, |Ch01.RealDistributionFunctions.distributionFunctionValue μ x -
          Ch01.RealDistributionFunctions.distributionFunctionValue ν x|) ≤
          C * ((∫ t in Icc (-T) T, ‖charFun μ t - charFun ν t‖ / |t|) + M / T)

end Specs.ProbabilityFoundations.Ch09.EsseenSmoothingInequality
