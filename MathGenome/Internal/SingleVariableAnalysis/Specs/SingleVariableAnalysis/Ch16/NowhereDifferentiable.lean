import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.TentContinuity
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Derivative

/-! Independent conclusions of K03.16.nowhere_differentiable,
paper.tex:3958–3998. The function is the canonical series of the 2-periodic
extension of |x| on [-1,1], with coefficients (3/4)^n and frequencies 4^n.
Sequence index m represents the paper's positive scale m+1. -/

namespace Specs.SingleVariableAnalysis.Ch16.NowhereDifferentiable

open Filter
open scoped Topology
open TentContinuity

/-- The counterexample is exactly the upstream canonical series. -/
def nowhereDifferentiableExampleType : Type := ℝ → ℝ

noncomputable def nowhereDifferentiableExampleValue : nowhereDifferentiableExampleType :=
  tentSeriesValue

/-- Signed half-cell increments tending to zero, with divergent quotient magnitudes. -/
def tentSeriesSmallIncrements : Prop :=
  ∀ x : ℝ, ∃ h : ℕ → ℝ,
    (∀ m, h m = (1 / 2 : ℝ) / 4 ^ (m + 1) ∨
      h m = -((1 / 2 : ℝ) / 4 ^ (m + 1))) ∧
    (∀ m, h m ≠ 0) ∧
    Tendsto h atTop (𝓝 0) ∧
    (∀ m, ((3 : ℝ) ^ (m + 1) + 1) / 2 ≤
      |(tentSeriesValue (x + h m) - tentSeriesValue x) / h m|) ∧
    Tendsto (fun m => |(tentSeriesValue (x + h m) - tentSeriesValue x) / h m|)
      atTop atTop

/-- No finite real-increment derivative exists, at any real argument. -/
def tentSeriesNoFiniteDerivative : Prop :=
  ∀ x L : ℝ, ¬ Ch04.Derivative.hasRealIncrementDerivativeValue tentSeriesValue L x

def tentSeriesNotDifferentiable : Prop :=
  ∀ x : ℝ, ¬ DifferentiableAt ℝ tentSeriesValue x

/-- The entire asserted counterexample, with no additional hypotheses. -/
def tentSeriesContinuousNowhereDifferentiable : Prop :=
  Continuous tentSeriesValue ∧ ∀ x : ℝ, ¬ DifferentiableAt ℝ tentSeriesValue x

end Specs.SingleVariableAnalysis.Ch16.NowhereDifferentiable
