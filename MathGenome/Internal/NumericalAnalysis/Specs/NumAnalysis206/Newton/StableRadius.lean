import Mathlib.Analysis.Real.Sqrt

/-! Independent types for the exact stable radius expression in Proposition W78.
The expressions use real arithmetic; no floating-point certificate is asserted. -/
namespace Specs.NumAnalysis206.Newton.StableRadius

/-- The rationalized denominator is strictly positive, including at L = 0. -/
def denominatorPositive : Prop :=
  ∀ η L : ℝ, 0 < 1 + Real.sqrt (1 - 2 * η * L)

/-- Equality with the semilocal radius, including zero residual and the critical case. -/
def radiusIdentity : Prop :=
  ∀ η L : ℝ, 0 < L → 0 ≤ 2 * η * L → 2 * η * L ≤ 1 →
    (1 - Real.sqrt (1 - 2 * η * L)) / L =
      2 * η / (1 + Real.sqrt (1 - 2 * η * L))

/-- The rationalized expression has the prescribed value at L = 0. -/
def radiusAtZero : Prop :=
  ∀ η : ℝ, 2 * η / (1 + Real.sqrt (1 - 2 * η * (0 : ℝ))) = η

/-- For fixed residual bound, the rationalized expression is continuous in L.
Together with the identity and value at zero, this supplies a continuous extension. -/
def radiusContinuous : Prop :=
  ∀ η : ℝ, Continuous (fun L : ℝ =>
    2 * η / (1 + Real.sqrt (1 - 2 * η * L)))

end Specs.NumAnalysis206.Newton.StableRadius
