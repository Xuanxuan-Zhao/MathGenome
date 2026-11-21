import MathGenome.Internal.SingleVariableAnalysis.D03SupportRepairs.CoefficientBounds
import MathGenome.Internal.SingleVariableAnalysis.D03SupportRepairs.FactorialTailComparison
import MathGenome.Internal.SingleVariableAnalysis.Specs.D03SupportRepairs.UniformNonnegativeRemainder

/-! The omitted binomial coefficients form a nonnegative summable tail,
bounded uniformly in the positive row by the inverse-factorial tail. -/

noncomputable section
open scoped BigOperators Topology

namespace D03SupportRepairs

/-- Canonical binomial coefficients vanish past the end of the row. -/
theorem b_eq_zero_of_lt (N j : ℕ) (hj : N < j) : b N j = 0 := by
  simp [b, Nat.choose_eq_zero_of_lt hj]

/-- The coefficient series is summable by the inverse-factorial comparison. -/
theorem b_summable (N : ℕ) (hN : 1 ≤ N) : Summable (b N) := by
  exact Summable.of_nonneg_of_le (fun j => (coefficientBounds N hN j).1)
    (fun j => (coefficientBounds N hN j).2) invFactorial_summable

/-- The full coefficient series is the finite binomial expansion. -/
theorem tsum_b (N : ℕ) (hN : 1 ≤ N) : (∑' j, b N j) = u N := by
  rw [tsum_eq_sum (s := Finset.range (N + 1))]
  · exact (finiteRepresentation N hN).symm
  · intro j hj
    apply b_eq_zero_of_lt N j
    simpa only [Finset.mem_range, not_lt, Nat.succ_le_iff] using hj

/-- The finite prefix is its zero-padded series. -/
theorem prefix_eq_tsum (N J : ℕ) :
    «prefix» N J = ∑' j : ℕ, if j ≤ J then b N j else 0 := by
  symm
  rw [tsum_eq_sum (s := Finset.range (J + 1))]
  · apply Finset.sum_congr rfl
    intro j hj
    simp only [ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  · intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    simp only [ite_eq_right (by omega : ¬j ≤ J)]

/-- Subtracting the prefix leaves precisely the strict tail, for every cutoff. -/
theorem remainder_eq_tsum (N : ℕ) (hN : 1 ≤ N) (J : ℕ) :
    u N - «prefix» N J = ∑' j : ℕ, if J < j then b N j else 0 := by
  have hp : Summable (fun j : ℕ => if j ≤ J then b N j else 0) := by
    refine ((b_summable N hN).indicator {j : ℕ | j ≤ J}).congr ?_
    intro j
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [← tsum_b N hN, prefix_eq_tsum, ← (b_summable N hN).tsum_sub hp]
  apply tsum_congr
  intro j
  by_cases hj : j ≤ J
  · simp [hj, Nat.not_lt_of_ge hj]
  · simp [hj, Nat.lt_of_not_ge hj]

/-- The strict coefficient tail is nonnegative and bounded by the factorial tail. -/
theorem remainderBounds (N : ℕ) (hN : 1 ≤ N) (J : ℕ) :
    0 ≤ u N - «prefix» N J ∧
    u N - «prefix» N J ≤ factorialTail J := by
  rw [remainder_eq_tsum N hN J]
  have ht : Summable (fun j : ℕ => if J < j then b N j else 0) := by
    refine ((b_summable N hN).indicator {j : ℕ | J < j}).congr ?_
    intro j
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  constructor
  · apply tsum_nonneg
    intro j
    split_ifs
    · exact (coefficientBounds N hN j).1
    · exact le_refl 0
  · apply Summable.tsum_le_tsum _ ht (factorialTail_summable J)
    intro j
    split_ifs
    · exact (coefficientBounds N hN j).2
    · exact le_refl 0

/-- The complete uniform comparison and decay conclusion of the source. -/
theorem uniformNonnegativeRemainder :
    (∀ (N : ℕ), 1 ≤ N → ∀ (J : ℕ),
      0 ≤ u N - «prefix» N J ∧
      u N - «prefix» N J ≤ factorialTail J ∧
      factorialTail J ≤ geometricTail J) ∧
    Filter.Tendsto geometricTail Filter.atTop (nhds (0 : ℝ)) := by
  refine ⟨?_, geometricTail_tendsto⟩
  intro N hN J
  exact ⟨(remainderBounds N hN J).1, (remainderBounds N hN J).2,
    factorialTail_le_geometricTail J⟩

/-- At every cutoff J ≥ N, including J = N, all omitted coefficients vanish. -/
theorem remainder_eq_zero (N : ℕ) (hN : 1 ≤ N) (J : ℕ) (hNJ : N ≤ J) :
    u N - «prefix» N J = 0 := by
  rw [remainder_eq_tsum N hN J]
  calc
    _ = ∑' _j : ℕ, (0 : ℝ) := by
      apply tsum_congr
      intro j
      split_ifs with hj
      · exact b_eq_zero_of_lt N j (lt_of_le_of_lt hNJ hj)
      · rfl
    _ = 0 := tsum_zero

end D03SupportRepairs
