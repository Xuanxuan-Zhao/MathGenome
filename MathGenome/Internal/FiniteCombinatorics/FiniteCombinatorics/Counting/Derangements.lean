import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Counting.Derangements
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The two derangement formulas of paper.tex, W04, including n = 0. -/

open scoped BigOperators

namespace FiniteCombinatorics.Counting

/-- The integer alternating sum counts actual fixed-point-free permutations. -/
theorem derangements_integer :
    Specs.FiniteCombinatorics.Counting.DerangementsInteger := by
  intro n
  rw [card_derangements_fin_eq_numDerangements, numDerangements_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Finset.mem_range_succ_iff.mp hj
  rw [Nat.ascFactorial_eq_factorial_mul_choose, Nat.add_sub_of_le hjn,
    Nat.choose_symm hjn, Nat.cast_mul]
  ring

/-- Factoring out n! gives the rational reciprocal-factorial formula. -/
theorem derangements_rational :
    Specs.FiniteCombinatorics.Counting.DerangementsRational := by
  intro n
  have h := congrArg (fun z : ℤ => (z : ℚ)) (derangements_integer n)
  simp only [Int.cast_natCast, Int.cast_sum, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one] at h
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Finset.mem_range_succ_iff.mp hj
  rw [Nat.cast_choose ℚ hjn]
  have hjf : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hnjf : ((n - j).factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - j))
  field_simp

/-- There is exactly one permutation, hence one derangement, of the empty set. -/
theorem derangements_zero :
    Specs.FiniteCombinatorics.Counting.DerangementsZero := by
  rw [Specs.FiniteCombinatorics.Counting.DerangementsZero,
    card_derangements_fin_eq_numDerangements, numDerangements_zero]

end FiniteCombinatorics.Counting
