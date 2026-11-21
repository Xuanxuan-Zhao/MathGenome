import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.RealPowers
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Comparison
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Geometric
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PSeries

/-!
# Real p-series

K03.11.geometric_p, paper.tex:1011–1020 (p-series assertion).
The source index starts at one, represented by n+1 here. We use the source's
constructed real power, and its upstream identification with Real.rpow only
at strictly positive bases. For p ≤ 0 the terms are at least one, violating
the term test. For 0 < p ≤ 1 harmonic comparison gives divergence. For
p > 1 the upstream condensation theorem reduces the series to the geometric
series with ratio 2^(1-p). The power identities and order lemmas used in this
reduction are the exp/log laws in Mathlib.Analysis.SpecialFunctions.Pow.Real;
no library p-series theorem or integral test is used.
-/

noncomputable section
namespace SingleVariableAnalysis

/-- Nonpositive p gives terms bounded below by one. -/
theorem p_series_term_ge_one (p : ℝ) (hp : p ≤ 0) (n : ℕ) :
    1 ≤ realPower ((n : ℝ) + 1) (-p) := by
  rw [realPower_eq_rpow _ (by positivity)]
  exact Real.one_le_rpow (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith) (neg_nonneg.mpr hp)

theorem p_series_nonpositive_terms_not_null (p : ℝ) (hp : p ≤ 0) :
    ¬ RealSequenceConverges (fun n : ℕ => realPower ((n : ℝ) + 1) (-p)) 0 := by
  intro h
  obtain ⟨N, hN⟩ := h 1 zero_lt_one
  have hsmall : |realPower ((N : ℝ) + 1) (-p) - 0| < 1 := hN N le_rfl
  rw [sub_zero, abs_of_pos (realPower_pos _ (by positivity) _)] at hsmall
  exact (not_lt_of_ge (p_series_term_ge_one p hp N)) hsmall

theorem p_series_diverges_of_nonpositive (p : ℝ) (hp : p ≤ 0) :
    RealSeriesDiverges (fun n : ℕ => realPower ((n : ℝ) + 1) (-p)) := by
  intro hc
  exact p_series_nonpositive_terms_not_null p hp (real_series_term_limit _ hc)

theorem p_series_harmonic_le (p : ℝ) (hp : p ≤ 1) (n : ℕ) :
    1 / ((n : ℝ) + 1) ≤ realPower ((n : ℝ) + 1) (-p) := by
  rw [realPower_eq_rpow _ (by positivity)]
  simpa only [Real.rpow_neg_one, one_div] using
    (Real.rpow_le_rpow_of_exponent_le (show 1 ≤ (n : ℝ) + 1 by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
      (show (-1 : ℝ) ≤ -p by linarith))

theorem p_series_diverges_of_pos_le_one (p : ℝ) (_hp : 0 < p) (hp1 : p ≤ 1) :
    RealSeriesDiverges (fun n : ℕ => realPower ((n : ℝ) + 1) (-p)) := by
  intro hc
  exact comparison_harmonic_diverges
    (real_series_comparison_of_nonnegative _ _ (fun n => by positivity)
      (p_series_harmonic_le p hp1) hc)

/-- The exact dyadic identity underlying the geometric reduction. -/
theorem p_series_condensed_term (p : ℝ) (k : ℕ) :
    (2 : ℝ)^k * (((2 : ℕ)^k : ℕ) : ℝ)^(-p) = ((2 : ℝ)^(1-p))^k := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_pow_comm (by norm_num)]
  rw [← mul_pow, Real.rpow_sub (by norm_num), Real.rpow_one,
    Real.rpow_neg (by norm_num)]
  simp only [div_eq_mul_inv]

theorem p_series_converges_of_one_lt (p : ℝ) (hp : 1 < p) :
    RealSeriesConverges (fun n : ℕ => realPower ((n : ℝ) + 1) (-p)) := by
  have ha : ∀ n : ℕ, 1 ≤ n → 0 ≤ (n : ℝ)^(-p) := by
    intro n hn
    exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hm : AntitoneOn (fun n : ℕ => (n : ℝ)^(-p)) (Set.Ici 1) := by
    intro m hm n _ hmn
    exact Real.rpow_le_rpow_of_nonpos
      (show 0 < (m : ℝ) by exact_mod_cast hm)
      (by exact_mod_cast hmn) (by linarith)
  have hq : |(2 : ℝ)^(1-p)| < 1 := by
    rw [abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hg := (real_geometric_series_converges_iff ((2 : ℝ)^(1-p))).mpr hq
  have hc : RealSeriesConverges
      (fun k : ℕ => (2 : ℝ)^k * (((2 : ℕ)^k : ℕ) : ℝ)^(-p)) := by
    simpa only [p_series_condensed_term] using hg
  have hs := (cauchy_condensation (fun n : ℕ => (n : ℝ)^(-p)) ha hm).mpr hc
  have heq : (fun n : ℕ => realPower ((n : ℝ) + 1) (-p)) =
      (fun n : ℕ => ((n+1 : ℕ) : ℝ)^(-p)) := by
    funext n
    rw [realPower_eq_rpow _ (by positivity), Nat.cast_add, Nat.cast_one]
  rw [heq]
  exact hs

theorem p_series_converges_iff (p : ℝ) :
    RealSeriesConverges (fun n : ℕ => realPower ((n : ℝ) + 1) (-p)) ↔ 1 < p := by
  constructor
  · intro hc
    by_contra hp
    have hp1 : p ≤ 1 := le_of_not_gt hp
    by_cases hp0 : p ≤ 0
    · exact p_series_diverges_of_nonpositive p hp0 hc
    · exact p_series_diverges_of_pos_le_one p (lt_of_not_ge hp0) hp1 hc
  · exact p_series_converges_of_one_lt p

theorem p_series_diverges_iff (p : ℝ) :
    RealSeriesDiverges (fun n : ℕ => realPower ((n : ℝ) + 1) (-p)) ↔ p ≤ 1 := by
  change (¬ RealSeriesConverges _) ↔ _
  rw [p_series_converges_iff, not_lt]

/-- Canonical positive-base notation has exactly the same convergence criterion. -/
theorem p_series_rpow_converges_iff (p : ℝ) :
    RealSeriesConverges (fun n : ℕ => ((n : ℝ) + 1)^(-p)) ↔ 1 < p := by
  have heq : (fun n : ℕ => realPower ((n : ℝ) + 1) (-p)) =
      (fun n : ℕ => ((n : ℝ) + 1)^(-p)) := by
    funext n
    exact realPower_eq_rpow _ (by positivity) _
  rw [← heq]
  exact p_series_converges_iff p

end SingleVariableAnalysis
