import Mathlib.Basic.Real.Basic
import Mathlib.Order.Interval.Set.Basic

namespace D03Supporting.Specs

/-- The polynomial difference estimate on the real interval `[0, r + 1]`. -/
def PolynomialDifferenceBound : Prop :=
  ∀ (m : ℕ), 1 ≤ m →
    ∀ (r : ℝ), 0 ≤ r →
      ∀ (u v : ℝ), u ∈ Set.Icc 0 (r + 1) → v ∈ Set.Icc 0 (r + 1) →
        |u ^ m - v ^ m| ≤ (m : ℝ) * (r + 1) ^ (m - 1) * |u - v|

end D03Supporting.Specs
