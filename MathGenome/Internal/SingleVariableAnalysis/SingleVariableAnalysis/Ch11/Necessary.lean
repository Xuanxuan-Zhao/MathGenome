import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.PartialSums
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Necessary
import Mathlib.Tactic.FieldSimp

/-!
# The Cauchy criterion, term test, and harmonic counterexample

K03.11.necessary, paper.tex:987–996. We first identify inclusive finite
series tails with differences of ordinary partial sums, then apply the
proved real/complex sequence Cauchy criteria. The singleton tail proves
the term test. Harmonic divergence is obtained from the manuscript's
dyadic blocks, each at least 1/2, and positivity between block endpoints.
-/

namespace SingleVariableAnalysis

open scoped BigOperators

/-- Inclusive finite tails, with no subtraction in the natural endpoints. -/
theorem sum_Icc_eq_sub_sum_range {A : Type*} [AddCommGroup A]
    (a : ℕ → A) {p q : ℕ} (hpq : p ≤ q) :
    (∑ n ∈ Finset.Icc p q, a n) =
      (∑ n ∈ Finset.range (q + 1), a n) - ∑ n ∈ Finset.range p, a n := by
  have he : Finset.Icc p q = Finset.Ico p (q + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff]
  rw [he, Finset.sum_Ico_eq_sub a (hpq.trans (Nat.le_succ q))]

/-- Finite algebra and tail bookkeeping, independent of completeness. -/
theorem partial_sums_cauchy_iff_tails {A : Type*} [NormedAddCommGroup A]
    (a : ℕ → A) :
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      ‖(∑ i ∈ Finset.range (n + 1), a i) - ∑ i ∈ Finset.range (m + 1), a i‖ < ε) ↔
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ p,
      ‖∑ i ∈ Finset.Icc p q, a i‖ < ε) := by
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N + 1, ?_⟩
    intro p hp q hpq
    rw [sum_Icc_eq_sub_sum_range a hpq]
    have hp0 : 1 ≤ p := (Nat.le_add_left 1 N).trans hp
    have hpN : N ≤ p - 1 := by omega
    simpa only [Nat.sub_add_cancel hp0] using hN (p - 1) hpN q (by omega)
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    have hlt : ∀ m ≥ N, ∀ n, m < n →
        ‖(∑ i ∈ Finset.range (n + 1), a i) - ∑ i ∈ Finset.range (m + 1), a i‖ < ε := by
      intro m hm n hmn
      simpa only [sum_Icc_eq_sub_sum_range a (Nat.succ_le_of_lt hmn)] using
        hN (m + 1) (by omega) n (by omega)
    refine ⟨N, ?_⟩
    intro m hm n hn
    rcases lt_trichotomy m n with hmn | hmn | hmn
    · exact hlt m hm n hmn
    · subst n
      simpa using hε
    · rw [norm_sub_rev]
      exact hlt n hn m hmn

theorem real_series_cauchy_criterion (a : ℕ → ℝ) :
    RealSeriesConverges a ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ p,
        |∑ n ∈ Finset.Icc p q, a n| < ε := by
  change (∃ S : ℝ, RealSequenceConverges (realPartialSum a) S) ↔ _
  rw [real_cauchy_criterion]
  simpa only [realPartialSum, Real.norm_eq_abs] using partial_sums_cauchy_iff_tails a

theorem complex_series_cauchy_criterion (a : ℕ → ℂ) :
    ComplexSeriesConverges a ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ p,
        ‖∑ n ∈ Finset.Icc p q, a n‖ < ε := by
  change (∃ S : ℂ, ComplexSequenceConverges (complexPartialSum a) S) ↔ _
  rw [complex_cauchy_criterion]
  exact partial_sums_cauchy_iff_tails a

theorem real_series_term_limit (a : ℕ → ℝ) (h : RealSeriesConverges a) :
    RealSequenceConverges a 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := (real_series_cauchy_criterion a).mp h ε hε
  exact ⟨N, fun n hn => by simpa using hN n hn n le_rfl⟩

theorem complex_series_term_limit (a : ℕ → ℂ) (h : ComplexSeriesConverges a) :
    ComplexSequenceConverges a 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := (complex_series_cauchy_criterion a).mp h ε hε
  exact ⟨N, fun n hn => by simpa using hN n hn n le_rfl⟩

theorem harmonic_term_limit :
    RealSequenceConverges (fun n : ℕ => 1 / (n : ℝ)) 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hbound : 1 / ε < (n : ℝ) := hN.trans_le (Nat.cast_le.mpr (by omega))
  simpa only [sub_zero, abs_of_pos (one_div_pos.mpr hnpos)] using
    (one_div_lt hnpos hε).mpr hbound

theorem harmonic_dyadic_block (k : ℕ) :
    (1 : ℝ) / 2 ≤ ∑ n ∈ Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1)), 1 / (n : ℝ) := by
  have hpow : 0 < (2 ^ k : ℝ) := pow_pos (by norm_num) k
  have hcard : (Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1))).card = 2 ^ k := by
    rw [Nat.card_Ico, pow_succ]
    omega
  calc
    (1 : ℝ) / 2 = ∑ _n ∈ Finset.Ico (2 ^ k : ℕ) (2 ^ (k + 1)),
        1 / (2 ^ (k + 1) : ℝ) := by
      simp only [Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [pow_succ]
      field_simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro n hn
      have hmem := Finset.mem_Ico.mp hn
      have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr
        (lt_of_lt_of_le (pow_pos (by omega : 0 < (2 : ℕ)) k) hmem.1)
      exact one_div_le_one_div_of_le hnpos (by exact_mod_cast hmem.2.le)

private theorem harmonic_dyadic_range_bound (k : ℕ) :
    (k : ℝ) / 2 ≤ ∑ n ∈ Finset.range (2 ^ k), 1 / (n : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hle : 2 ^ k ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega
    rw [← Finset.sum_range_add_sum_Ico (fun n : ℕ => 1 / (n : ℝ)) hle]
    have hb := harmonic_dyadic_block k
    push_cast
    linarith

theorem harmonic_dyadic_partialSum_lower_bound (k : ℕ) :
    (k : ℝ) / 2 ≤ realPartialSum (fun n : ℕ => 1 / (n : ℝ)) (2 ^ k - 1) := by
  simpa only [realPartialSum, Nat.sub_add_cancel Nat.one_le_two_pow] using
    harmonic_dyadic_range_bound k

private theorem harmonic_partialSum_monotone :
    Monotone (realPartialSum (fun n : ℕ => 1 / (n : ℝ))) := by
  intro m n hmn
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right hmn 1))
  intro i _ _
  exact one_div_nonneg.mpr (Nat.cast_nonneg i)

theorem harmonic_partialSums_unbounded (B : ℝ) :
    ∃ N : ℕ, B < realPartialSum (fun n : ℕ => 1 / (n : ℝ)) N := by
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * B)
  refine ⟨2 ^ k - 1, ?_⟩
  have hb := harmonic_dyadic_partialSum_lower_bound k
  linarith

theorem harmonic_divergesToPosInfinity :
    DivergesToPosInfinity (realPartialSum (fun n : ℕ => 1 / (n : ℝ))) := by
  intro B
  obtain ⟨N, hN⟩ := harmonic_partialSums_unbounded B
  exact ⟨N, fun n hn => hN.trans_le (harmonic_partialSum_monotone hn)⟩

theorem harmonic_series_diverges :
    RealSeriesDiverges (fun n : ℕ => 1 / (n : ℝ)) := by
  rintro ⟨S, hS⟩
  exact posInfinity_not_finite _ harmonic_divergesToPosInfinity S hS

end SingleVariableAnalysis
