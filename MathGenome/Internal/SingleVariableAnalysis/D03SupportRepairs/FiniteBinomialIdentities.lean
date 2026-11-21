import MathGenome.Internal.SingleVariableAnalysis.D03SupportRepairs.BinomialQuantities
import MathGenome.Internal.SingleVariableAnalysis.Specs.D03SupportRepairs.FiniteBinomialIdentities
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.FieldSimp

noncomputable section
open scoped BigOperators

namespace D03SupportRepairs

/-- Binomial expansion of the positive row. -/
theorem finiteRepresentation (N : ℕ) (_hN : 1 ≤ N) :
    u N = ∑ j ∈ Finset.range (N + 1), b N j := by
  unfold u b
  rw [add_comm, add_pow]
  apply Finset.sum_congr rfl
  intro j _hj
  simp [div_eq_mul_inv, mul_comm]

/-- Product formula on the source range j ≤ N. -/
theorem coefficientProduct (N : ℕ) (hN : 1 ≤ N) (j : ℕ) (hj : j ≤ N) :
    b N j = invFactorial j *
      ∏ ℓ ∈ Finset.range j, (1 - (ℓ : ℝ) / (N : ℝ)) := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hf : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hprod : (∏ ℓ ∈ Finset.range j, ((N : ℝ) - (ℓ : ℝ))) =
      (j.factorial : ℝ) * (N.choose j : ℝ) := by
    calc
      _ = ∏ ℓ ∈ Finset.range j, ((N - ℓ : ℕ) : ℝ) := by
        apply Finset.prod_congr rfl
        intro ℓ hℓ
        rw [Nat.cast_sub ((Finset.mem_range.mp hℓ).le.trans hj)]
      _ = (N.descFactorial j : ℝ) := by
        rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
      _ = _ := by rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hterm (ℓ : ℕ) :
      (1 - (ℓ : ℝ) / (N : ℝ)) = ((N : ℝ) - (ℓ : ℝ)) / (N : ℝ) := by
    field_simp
  have hnormalized : (∏ ℓ ∈ Finset.range j, (1 - (ℓ : ℝ) / (N : ℝ))) =
      ((j.factorial : ℝ) * (N.choose j : ℝ)) / (N : ℝ) ^ j := by
    simp_rw [hterm]
    rw [Finset.prod_div_distrib, hprod]
    simp
  rw [hnormalized]
  unfold b invFactorial
  rw [one_div, ← mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ hf, one_mul]

end D03SupportRepairs
