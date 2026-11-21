import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.EquispacedLebesgue

/-! Independent specification for the single continuous witness in W54.
The operators act on the continuous real functions with the uniform norm.
Their values are precisely the endpoint-grid interpolation polynomials,
embedded in the same function space as in W52. -/
noncomputable section
namespace Specs.NumAnalysis206.Approximation
open _root_.NumAnalysis206.Approximation

/-- One function has interpolation norms exceeding every real bound, at degrees ≥ 2. -/
def equispacedUnbounded : Prop :=
  ∀ (a b : ℝ) (hab : a < b),
    ∃ f : IntervalContinuous a b, ∀ B : ℝ,
      ∃ (n : ℕ) (hn : 2 ≤ n),
        B < ‖interpolationOperatorValue
          (equispacedNodesValue a b hab n (lt_of_lt_of_le (by decide) hn)) f‖

end Specs.NumAnalysis206.Approximation
