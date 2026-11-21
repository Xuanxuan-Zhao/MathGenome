import MathGenome.Internal.SingleVariableAnalysis.Specs.D03Supporting.BinomialCoefficientLowerBound
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace D03Supporting

/-- For `n ≥ 2m`, each falling-factorial factor is at least `n/2`. -/
theorem binomial_coefficient_lower_bound :
    Specs.D03Supporting.BinomialCoefficientLowerBound := by
  intro m n _hm hnm
  have hmn : m ≤ n + 1 := by omega
  have hnm_real : (2 : ℝ) * (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnm
  have hsub : ((n + 1 - m : ℕ) : ℝ) = (n : ℝ) + 1 - (m : ℝ) := by
    rw [Nat.cast_sub hmn]
    push_cast
    rfl
  have hbase : (n : ℝ) / 2 ≤ ((n + 1 - m : ℕ) : ℝ) := by
    rw [hsub]
    linarith
  calc
    ((n : ℝ) / 2) ^ m / (m.factorial : ℝ) ≤
        ((n + 1 - m : ℕ) : ℝ) ^ m / (m.factorial : ℝ) := by
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hbase m) (by positivity)
    _ ≤ (Nat.choose n m : ℝ) := Nat.pow_le_choose m n

end D03Supporting
