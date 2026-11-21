import MathGenome.Internal.SingleVariableAnalysis.D03SupportRepairs.FiniteBinomialIdentities
import MathGenome.Internal.SingleVariableAnalysis.Specs.D03SupportRepairs.CoefficientBounds
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

noncomputable section
open scoped BigOperators

namespace D03SupportRepairs

/-- Every coefficient in a positive row is nonnegative and bounded by 1/j!,
including the zero coefficients beyond the end of that row. -/
theorem coefficientBounds (N : ℕ) (hN : 1 ≤ N) (j : ℕ) :
    0 ≤ b N j ∧ b N j ≤ invFactorial j := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hf : 0 ≤ invFactorial j :=
    div_nonneg zero_le_one (Nat.cast_nonneg _)
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg hn.le _)
  · by_cases hj : j ≤ N
    · rw [coefficientProduct N hN j hj]
      apply mul_le_of_le_one_right hf
      apply Finset.prod_le_one₀
      · intro ℓ hℓ
        apply sub_nonneg.mpr
        apply (div_le_one hn).mpr
        exact Nat.cast_le.mpr ((Finset.mem_range.mp hℓ).le.trans hj)
      · intro ℓ _hℓ
        exact sub_le_self _ (div_nonneg (Nat.cast_nonneg _) hn.le)
    · have hz : N.choose j = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hj)
      simpa [b, hz] using hf

/-- The complete source theorem, reusing the two established finite identities. -/
theorem finiteRepresentationAndCoefficientBounds (N : ℕ) (hN : 1 ≤ N) :
    (u N = ∑ j ∈ Finset.range (N + 1), b N j) ∧
    (∀ (j : ℕ), j ≤ N →
      b N j = invFactorial j *
        ∏ ℓ ∈ Finset.range j, (1 - (ℓ : ℝ) / (N : ℝ))) ∧
    (∀ (j : ℕ), 0 ≤ b N j ∧ b N j ≤ invFactorial j) := by
  exact ⟨finiteRepresentation N hN, coefficientProduct N hN, coefficientBounds N hN⟩

end D03SupportRepairs
