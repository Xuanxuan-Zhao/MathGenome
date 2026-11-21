import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Logic.Function.Iterate

/-!
Independent specification of paper.tex, Proposition p206:W69, under the
hypotheses of Theorem p206:W66. The point `p` is any fixed point of `T`;
W66 supplies its existence and uniqueness. Both estimates hold for every
start and every natural-number index, with no exclusion of `q = 0`.
-/

universe u

namespace Specs.NumAnalysis206.Iterations

/-- The a priori and a posteriori error estimates for exact contraction iteration. -/
def FixedPointErrorBoundsStatement : Prop :=
  ∀ (X : Type u) [MetricSpace X] [Nonempty X] [CompleteSpace X]
    (T : X → X) (q : ℝ),
    0 ≤ q → q < 1 →
    (∀ x y : X, dist (T x) (T y) ≤ q * dist x y) →
    ∀ p : X, T p = p → ∀ (x₀ : X) (n : ℕ),
      dist (T^[n] x₀) p ≤ q ^ n * dist (T x₀) x₀ / (1 - q) ∧
      dist (T^[n] x₀) p ≤ dist (T^[n + 1] x₀) (T^[n] x₀) / (1 - q)

end Specs.NumAnalysis206.Iterations
