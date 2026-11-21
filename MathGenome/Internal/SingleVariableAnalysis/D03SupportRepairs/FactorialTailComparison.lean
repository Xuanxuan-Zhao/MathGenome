import MathGenome.Internal.SingleVariableAnalysis.D03SupportRepairs.GeometricTailConvergence
import MathGenome.Internal.SingleVariableAnalysis.Specs.D03SupportRepairs.FactorialTailComparison
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.Ring

/-! Comparison of the actual inverse-factorial series and its strict tails
with the summable geometric majorant from the source. -/

namespace D03SupportRepairs

/-- Every inverse factorial is nonnegative. -/
theorem invFactorial_nonneg (j : ℕ) : 0 ≤ invFactorial j := by
  unfold invFactorial
  positivity

/-- Since `2^n ≤ (n+1)!`, the geometric term majorizes every inverse factorial. -/
theorem invFactorial_le_geomTerm (j : ℕ) : invFactorial j ≤ geomTerm j := by
  cases j with
  | zero => norm_num [invFactorial, geomTerm]
  | succ n =>
    have hnat : 2 ^ n ≤ (n + 1).factorial := by
      simpa [Nat.add_comm] using
        (Nat.factorial_mul_pow_le_factorial (m := 1) (n := n))
    have hreal : (2 : ℝ) ^ n ≤ ((n + 1).factorial : ℝ) := by
      exact_mod_cast hnat
    calc
      invFactorial (n + 1) ≤ 1 / (2 : ℝ) ^ n :=
        one_div_le_one_div_of_le (pow_pos (by norm_num) n) hreal
      _ = geomTerm (n + 1) := by
        unfold geomTerm
        rw [one_div_pow, pow_succ]
        ring

/-- Comparison with the summable geometric series gives factorial summability. -/
theorem invFactorial_summable : Summable (fun j : ℕ => invFactorial j) := by
  exact Summable.of_nonneg_of_le invFactorial_nonneg invFactorial_le_geomTerm
    geomTerm_summable

/-- Restricting the inverse-factorial series to a strict tail preserves summability. -/
theorem factorialTail_summable (J : ℕ) :
    Summable (fun j : ℕ => if J < j then invFactorial j else 0) := by
  refine (invFactorial_summable.indicator {j : ℕ | J < j}).congr ?_
  intro j
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]

/-- The actual inverse-factorial tail has nonnegative terms. -/
theorem factorialTail_nonneg (J : ℕ) : 0 ≤ factorialTail J := by
  apply tsum_nonneg
  intro j
  split_ifs
  · exact invFactorial_nonneg j
  · exact le_refl 0

/-- Termwise comparison of the two summable strict tails gives the source bound. -/
theorem factorialTail_le_geometricTail (J : ℕ) : factorialTail J ≤ geometricTail J := by
  apply Summable.tsum_le_tsum _ (factorialTail_summable J) (geometricTail_summable J)
  intro j
  split_ifs
  · exact invFactorial_le_geomTerm j
  · exact le_refl 0

end D03SupportRepairs
