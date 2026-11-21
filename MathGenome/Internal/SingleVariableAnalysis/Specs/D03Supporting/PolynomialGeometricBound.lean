import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Basic

namespace Specs.D03Supporting

/-- The four explicit inequalities for every `n ≥ 2 * (k + 1)`. -/
def PolynomialGeometricBound : Prop :=
  ∀ (k n : ℕ) (r : ℝ), 1 < r →
    let m := k + 1
    let d := r - 1
    2 * m ≤ n →
      (Nat.choose n m : ℝ) * d ^ m ≤ r ^ n ∧
      (((n : ℝ) / 2) ^ m * d ^ m) / (m.factorial : ℝ) ≤
        (Nat.choose n m : ℝ) * d ^ m ∧
      0 ≤ (n : ℝ) ^ k / r ^ n ∧
      (n : ℝ) ^ k / r ^ n ≤
        ((2 : ℝ) ^ m * (m.factorial : ℝ)) / (d ^ m * (n : ℝ))

end Specs.D03Supporting
