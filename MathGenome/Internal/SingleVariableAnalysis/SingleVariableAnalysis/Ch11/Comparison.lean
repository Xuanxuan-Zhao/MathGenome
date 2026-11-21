import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Nonnegative
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Condensation
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Comparison
import Mathlib.Tactic.FieldSimp

/-!
# Comparison and limit comparison of ordinary real series

K03.11.comparison, paper.tex:1003–1011. Finite prefixes are removed by
the exact upstream finite-change theorem. Partial-sum boundedness then
proves comparison, including nonpositive comparison constants. Positive
finite ratios give two eventual comparisons; zero and infinite ratios give
the respective one-way comparisons. The examples use condensation and the
geometric series, with an explicit bridge to ordinary inclusive partial sums.
-/

namespace SingleVariableAnalysis

open scoped BigOperators Topology

/-- A globally nonnegative minorant of any convergent real series converges. -/
theorem real_series_comparison_of_nonnegative (a b : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hle : ∀ n, a n ≤ b n)
    (hb : RealSeriesConverges b) : RealSeriesConverges a := by
  obtain ⟨S, hS⟩ := hb
  obtain ⟨D, _, hD⟩ := real_convergent_bounded (realPartialSum b) S hS
  apply (nonnegative_series_converges_iff a ha).mpr
  refine ⟨D, ?_⟩
  rintro _ ⟨N, rfl⟩
  exact (Finset.sum_le_sum (fun n _ => hle n)).trans
    ((le_abs_self (realPartialSum b N)).trans (hD N))

theorem real_series_comparison (a b : ℕ → ℝ) (C : ℝ)
    (ha : SequenceEventually (fun n => 0 ≤ a n))
    (_hb : SequenceEventually (fun n => 0 ≤ b n))
    (hle : SequenceEventually (fun n => a n ≤ C * b n))
    (hconv : RealSeriesConverges b) : RealSeriesConverges a := by
  obtain ⟨N, hN⟩ := ha
  obtain ⟨M, hM⟩ := hle
  let K := max N M
  let a' := fun n => if K ≤ n then a n else 0
  let b' := fun n => if K ≤ n then b n else 0
  have hea : RealSeriesConverges a ↔ RealSeriesConverges a' :=
    real_series_finite_changes_iff a a' K (fun n hn => ite_eq_left hn.le)
  have heb : RealSeriesConverges b ↔ RealSeriesConverges b' :=
    real_series_finite_changes_iff b b' K (fun n hn => ite_eq_left hn.le)
  have ha' : ∀ n, 0 ≤ a' n := by
    intro n
    dsimp [a']
    split_ifs with hn
    · exact hN n ((le_max_left N M).trans hn)
    · exact le_rfl
  have hle' : ∀ n, a' n ≤ C * b' n := by
    intro n
    dsimp [a', b']
    split_ifs with hn
    · exact hM n ((le_max_right N M).trans hn)
    · simp
  obtain ⟨S, hS⟩ := heb.mp hconv
  exact hea.mpr (real_series_comparison_of_nonnegative a' (fun n => C * b' n)
    ha' hle' ⟨C * S, real_series_const_mul b' S hS C⟩)

theorem real_series_comparison_divergence (a b : ℕ → ℝ) (C : ℝ)
    (ha : SequenceEventually (fun n => 0 ≤ a n))
    (hb : SequenceEventually (fun n => 0 ≤ b n))
    (hle : SequenceEventually (fun n => a n ≤ C * b n))
    (hd : RealSeriesDiverges a) : RealSeriesDiverges b :=
  fun hc => hd (real_series_comparison a b C ha hb hle hc)

theorem real_series_limit_comparison_positive (a b : ℕ → ℝ) (L : ℝ)
    (ha : SequenceEventually (fun n => 0 ≤ a n))
    (hb : SequenceEventually (fun n => 0 < b n)) (hL : 0 < L)
    (hlim : RealSequenceConverges (fun n => a n / b n) L) :
    RealSeriesConverges a ↔ RealSeriesConverges b := by
  obtain ⟨N, hN⟩ := hlim (L / 2) (half_pos hL)
  obtain ⟨M, hM⟩ := hb
  have hb0 : SequenceEventually (fun n => 0 ≤ b n) :=
    ⟨M, fun n hn => (hM n hn).le⟩
  have hu : SequenceEventually (fun n => a n ≤ (2 * L) * b n) := by
    refine ⟨max N M, fun n hn => ?_⟩
    apply (div_le_iff₀ (hM n ((le_max_right N M).trans hn))).mp
    have hh := (abs_lt.mp (hN n ((le_max_left N M).trans hn))).2
    linarith
  have hl : SequenceEventually (fun n => b n ≤ (2 / L) * a n) := by
    refine ⟨max N M, fun n hn => ?_⟩
    have hh := (abs_lt.mp (hN n ((le_max_left N M).trans hn))).1
    have hh' : L / 2 ≤ a n / b n := by linarith
    have hh'' := (le_div_iff₀ (hM n ((le_max_right N M).trans hn))).mp hh'
    change b n ≤ (2 / L) * a n
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hL).mpr
    nlinarith
  exact ⟨real_series_comparison b a (2 / L) hb0 ha hl,
    real_series_comparison a b (2 * L) ha hb0 hu⟩

theorem real_series_limit_comparison_zero (a b : ℕ → ℝ)
    (ha : SequenceEventually (fun n => 0 ≤ a n))
    (hb : SequenceEventually (fun n => 0 < b n))
    (hlim : RealSequenceConverges (fun n => a n / b n) 0)
    (hconv : RealSeriesConverges b) : RealSeriesConverges a := by
  obtain ⟨N, hN⟩ := hlim 1 zero_lt_one
  obtain ⟨M, hM⟩ := hb
  apply real_series_comparison a b 1 ha ⟨M, fun n hn => (hM n hn).le⟩ ?_ hconv
  refine ⟨max N M, fun n hn => ?_⟩
  apply (div_le_iff₀ (hM n ((le_max_right N M).trans hn))).mp
  have hh := (abs_lt.mp (hN n ((le_max_left N M).trans hn))).2
  linarith

theorem real_series_limit_comparison_infinity (a b : ℕ → ℝ)
    (ha : SequenceEventually (fun n => 0 ≤ a n))
    (hb : SequenceEventually (fun n => 0 < b n))
    (hlim : DivergesToPosInfinity (fun n => a n / b n))
    (hconv : RealSeriesConverges a) : RealSeriesConverges b := by
  obtain ⟨N, hN⟩ := hlim 1
  obtain ⟨M, hM⟩ := hb
  apply real_series_comparison b a 1 ⟨M, fun n hn => (hM n hn).le⟩ ha ?_ hconv
  refine ⟨max N M, fun n hn => ?_⟩
  have hh := (le_div_iff₀ (hM n ((le_max_right N M).trans hn))).mp
    (hN n ((le_max_left N M).trans hn)).le
  simpa only [one_mul] using hh

/-- The constant-one series has unbounded inclusive partial sums. -/
theorem real_series_ones_diverges : RealSeriesDiverges (fun _ : ℕ => (1 : ℝ)) := by
  intro hc
  obtain ⟨D, hD⟩ := (nonnegative_series_converges_iff _ (fun _ => zero_le_one)).mp hc
  obtain ⟨N, hN⟩ := exists_nat_gt D
  have hh : (N : ℝ) + 1 ≤ D := by
    simpa [realPartialSum] using hD ⟨N, rfl⟩
  linarith

/-- Harmonic divergence obtained from the upstream condensation equivalence. -/
theorem comparison_harmonic_diverges :
    RealSeriesDiverges (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
  have ha : ∀ n : ℕ, 1 ≤ n → 0 ≤ 1 / (n : ℝ) := by
    intro n hn
    positivity
  have hm : AntitoneOn (fun n : ℕ => 1 / (n : ℝ)) (Set.Ici 1) := by
    intro m hm n hn hmn
    exact one_div_le_one_div_of_le (by exact_mod_cast hm) (by exact_mod_cast hmn)
  intro hc
  have hh := (cauchy_condensation (fun n : ℕ => 1 / (n : ℝ)) ha hm).mp
    (by simpa only [Nat.cast_add, Nat.cast_one] using hc)
  apply real_series_ones_diverges
  simpa [Nat.cast_pow] using hh

/-- The reciprocal-square series converges by condensation to ratio 1/2. -/
theorem comparison_reciprocal_square_converges :
    RealSeriesConverges (fun n : ℕ => 1 / ((n : ℝ) + 1)^2) := by
  have ha : ∀ n : ℕ, 1 ≤ n → 0 ≤ 1 / (n : ℝ)^2 := by
    intro n hn
    positivity
  have hm : AntitoneOn (fun n : ℕ => 1 / (n : ℝ)^2) (Set.Ici 1) := by
    intro m hm n hn hmn
    have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
    exact one_div_le_one_div_of_le (sq_pos_of_pos hm0)
      (pow_le_pow_left₀ hm0.le (by exact_mod_cast hmn) 2)
  have heq : (fun k : ℕ => (2 : ℝ)^k * (1 / ((((2 : ℕ)^k : ℕ) : ℝ)^2))) =
      (fun k : ℕ => (1 / 2 : ℝ)^k) := by
    funext k
    simp only [Nat.cast_pow, Nat.cast_ofNat, div_pow, one_pow]
    field_simp
  have hg : RealSeriesConverges (fun k : ℕ => (1 / 2 : ℝ)^k) := by
    apply (nonnegative_series_converges_iff _ (fun k => by positivity)).mpr
    refine ⟨2, ?_⟩
    rintro _ ⟨N, rfl⟩
    exact sum_geometric_two_le (N + 1)
  have hc := (cauchy_condensation (fun n : ℕ => 1 / (n : ℝ)^2) ha hm).mpr
    (heq.symm ▸ hg)
  simpa only [Nat.cast_add, Nat.cast_one] using hc

theorem real_series_zero_limit_counterexample :
    (∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1)^2 ∧ 0 < 1 / ((n : ℝ) + 1)) ∧
      RealSequenceConverges
        (fun n => (1 / ((n : ℝ) + 1)^2) / (1 / ((n : ℝ) + 1))) 0 ∧
      RealSeriesConverges (fun n => 1 / ((n : ℝ) + 1)^2) ∧
      RealSeriesDiverges (fun n => 1 / ((n : ℝ) + 1)) := by
  refine ⟨fun n => ⟨by positivity, by positivity⟩, ?_,
    comparison_reciprocal_square_converges, comparison_harmonic_diverges⟩
  have heq : (fun n : ℕ => (1 / ((n : ℝ) + 1)^2) / (1 / ((n : ℝ) + 1))) =
      (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    funext n
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  rw [heq]
  exact (realSequenceConverges_iff _ _).mpr tendsto_one_div_add_atTop_nhds_zero_nat

theorem real_series_infinite_limit_counterexample :
    (∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) ∧ 0 < 1 / ((n : ℝ) + 1)^2) ∧
      DivergesToPosInfinity
        (fun n => (1 / ((n : ℝ) + 1)) / (1 / ((n : ℝ) + 1)^2)) ∧
      RealSeriesDiverges (fun n => 1 / ((n : ℝ) + 1)) ∧
      RealSeriesConverges (fun n => 1 / ((n : ℝ) + 1)^2) := by
  refine ⟨fun n => ⟨by positivity, by positivity⟩, ?_,
    comparison_harmonic_diverges, comparison_reciprocal_square_converges⟩
  have heq : (fun n : ℕ => (1 / ((n : ℝ) + 1)) / (1 / ((n : ℝ) + 1)^2)) =
      (fun n : ℕ => (n : ℝ) + 1) := by
    funext n
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  rw [heq]
  intro B
  obtain ⟨N, hN⟩ := exists_nat_gt B
  refine ⟨N, fun n hn => ?_⟩
  have hle : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

end SingleVariableAnalysis
