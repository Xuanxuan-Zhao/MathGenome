import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Basic

namespace Specs.D03Supporting

/-- The coefficient estimate in the explicit polynomial versus geometric bound.
All divisions and powers after casting are in the real numbers. -/
def BinomialCoefficientLowerBound : Prop :=
  ∀ (m n : ℕ), 1 ≤ m → 2 * m ≤ n →
    ((n : ℝ) / 2) ^ m / (m.factorial : ℝ) ≤ (Nat.choose n m : ℝ)

end Specs.D03Supporting
