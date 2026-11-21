import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Nonnegative
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Condensation
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Cauchy condensation

K03.11.condensation, paper.tex:1035–1047. Only the positive indices of a
are constrained. Finite dyadic block comparisons and nonnegativity control
all partial sums. The ordinary convergence equivalence then follows from
the upstream boundedness criterion for nonnegative series.
-/

namespace SingleVariableAnalysis

open scoped BigOperators

/-- Upper and lower estimates for each complete dyadic block. -/
theorem dyadic_block_bounds (a : ℕ → ℝ) (_ha : ∀ n, 1 ≤ n → 0 ≤ a n)
    (hm : AntitoneOn a (Set.Ici 1)) (k : ℕ) :
    (2 : ℝ)^k * a (2^(k+1)) ≤
      ∑ n ∈ Finset.Ico (2^k) (2^(k+1)), a n ∧
    (∑ n ∈ Finset.Ico (2^k) (2^(k+1)), a n) ≤
      (2 : ℝ)^k * a (2^k) := by
  have hcard : (Finset.Ico (2^k) (2^(k+1))).card = 2^k := by
    simp [pow_succ, mul_two]
  have hpos : 1 ≤ (2:ℕ)^k := Nat.one_le_two_pow
  have hnext : 1 ≤ (2:ℕ)^(k+1) := Nat.one_le_two_pow
  constructor
  · calc
      (2 : ℝ)^k * a (2^(k+1)) =
          ∑ _n ∈ Finset.Ico (2^k) (2^(k+1)), a (2^(k+1)) := by
            simp [hcard]
      _ ≤ ∑ n ∈ Finset.Ico (2^k) (2^(k+1)), a n := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hnl, hnu⟩ := Finset.mem_Ico.mp hn
        exact hm (hpos.trans hnl) hnext hnu.le
  · calc
      (∑ n ∈ Finset.Ico (2^k) (2^(k+1)), a n) ≤
          ∑ _n ∈ Finset.Ico (2^k) (2^(k+1)), a (2^k) := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hnl, _⟩ := Finset.mem_Ico.mp hn
        exact hm hpos (hpos.trans hnl) hnl
      _ = (2 : ℝ)^k * a (2^k) := by simp [hcard]

/-- Summing the block estimates, with the exact half-shifted lower bound. -/
theorem dyadic_partialSum_bounds (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ n → 0 ≤ a n)
    (hm : AntitoneOn a (Set.Ici 1)) (K : ℕ) :
    ((∑ k ∈ Finset.range (K+1), (2 : ℝ)^k * a (2^k)) - a 1) / 2 ≤
      ∑ n ∈ Finset.Ico 1 (2^K), a n ∧
    (∑ n ∈ Finset.Ico 1 (2^K), a n) ≤
      ∑ k ∈ Finset.range K, (2 : ℝ)^k * a (2^k) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hb := dyadic_block_bounds a ha hm K
    have hs : (∑ n ∈ Finset.Ico 1 (2^(K+1)), a n) =
        (∑ n ∈ Finset.Ico 1 (2^K), a n) +
        ∑ n ∈ Finset.Ico (2^K) (2^(K+1)), a n := by
      exact (Finset.sum_Ico_consecutive a Nat.one_le_two_pow
        (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_succ K))).symm
    rw [hs]
    constructor
    · rw [Finset.sum_range_succ]
      rw [pow_succ (2 : ℝ) K]
      nlinarith [ih.1, hb.1]
    · rw [Finset.sum_range_succ]
      exact add_le_add ih.2 hb.2

/-- Bound every intermediate initial segment by a condensed initial segment. -/
theorem dyadic_intermediate_partialSum_bound (a : ℕ → ℝ)
    (ha : ∀ n, 1 ≤ n → 0 ≤ a n) (hm : AntitoneOn a (Set.Ici 1))
    (N K : ℕ) (hN : N ≤ 2^K) :
    (∑ n ∈ Finset.Ico 1 N, a n) ≤
      ∑ k ∈ Finset.range K, (2 : ℝ)^k * a (2^k) := by
  apply le_trans ?_ (dyadic_partialSum_bounds a ha hm K).2
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨hnl, hnu⟩ := Finset.mem_Ico.mp hn
    exact Finset.mem_Ico.mpr ⟨hnl, hnu.trans_le hN⟩
  · intro n hn _
    exact ha n (Finset.mem_Ico.mp hn).1

/-- Positive-index initial segments are monotone in their exclusive endpoint. -/
theorem positive_initial_sum_mono (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ n → 0 ≤ a n)
    {N M : ℕ} (hNM : N ≤ M) :
    (∑ n ∈ Finset.Ico 1 N, a n) ≤ ∑ n ∈ Finset.Ico 1 M, a n := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨hnl, hnu⟩ := Finset.mem_Ico.mp hn
    exact Finset.mem_Ico.mpr ⟨hnl, hnu.trans_le hNM⟩
  · intro n hn _
    exact ha n (Finset.mem_Ico.mp hn).1

/-- The exact bridge from the source's positive indices to upstream partial sums. -/
theorem positive_partialSum_eq (a : ℕ → ℝ) (N : ℕ) :
    realPartialSum (fun n => a (n+1)) N = ∑ n ∈ Finset.Ico 1 (N+2), a n := by
  simp [realPartialSum, Finset.sum_Ico_eq_sum_range, Nat.add_comm]

/-- Cauchy condensation for ordinary series, without any condition on a 0. -/
theorem cauchy_condensation (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ n → 0 ≤ a n)
    (hm : AntitoneOn a (Set.Ici 1)) :
    RealSeriesConverges (fun n => a (n+1)) ↔
      RealSeriesConverges (fun k => (2 : ℝ)^k * a (2^k)) := by
  have hp : ∀ n : ℕ, 0 ≤ a (n+1) := fun n => ha (n+1) (Nat.succ_le_succ (Nat.zero_le n))
  have hc : ∀ k : ℕ, 0 ≤ (2 : ℝ)^k * a (2^k) :=
    fun k => mul_nonneg (by positivity) (ha (2^k) Nat.one_le_two_pow)
  rw [nonnegative_series_converges_iff _ hp, nonnegative_series_converges_iff _ hc]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨2*C + a 1, ?_⟩
    rintro _ ⟨K, rfl⟩
    have hl := (dyadic_partialSum_bounds a ha hm K).1
    have hu : (∑ n ∈ Finset.Ico 1 (2^K), a n) ≤ C := by
      calc
        (∑ n ∈ Finset.Ico 1 (2^K), a n) ≤
            ∑ n ∈ Finset.Ico 1 (2^K+2), a n :=
          positive_initial_sum_mono a ha (Nat.le_add_right _ _)
        _ = realPartialSum (fun n => a (n+1)) (2^K) := (positive_partialSum_eq a _).symm
        _ ≤ C := hC ⟨2^K, rfl⟩
    change (realPartialSum (fun k => (2 : ℝ)^k * a (2^k)) K - a 1) / 2 ≤ _ at hl
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro _ ⟨N, rfl⟩
    rw [positive_partialSum_eq]
    exact (dyadic_intermediate_partialSum_bound a ha hm (N+2) (N+2)
      (Nat.lt_two_pow_self.le)).trans (hC ⟨N+1, rfl⟩)

end SingleVariableAnalysis
