import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Radius
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Ratio
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.RatioRadius

/-!
# Ratio formula for the Cauchy–Hadamard radius

K03.13.ratio_radius. At every positive distance t, the term ratio has
extended limit tℓ. Strictly inside ℓ⁻¹ it is eventually bounded by a
fixed q < 1, so geometric comparison gives absolute convergence.
Strictly outside, it is eventually greater than one, so the ordinary
term test gives divergence. The already proved uniqueness of the radius
identifies ℓ⁻¹ with the original root-limsup definition. The inverse-ratio
form follows from continuity of reciprocal on ENNReal, including 0 and ∞.
-/
noncomputable section
namespace SingleVariableAnalysis
open Filter
open scoped Topology ENNReal

namespace PowerSeriesRatio

/-- An extended ratio limit strictly below one yields a geometric contraction. -/
theorem contraction_of_limit (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (hn : SequenceEventually (fun n => b n ≠ 0)) (L : ℝ≥0∞)
    (hL : Tendsto (fun n => ENNReal.ofReal (b (n+1) / b n)) atTop (𝓝 L))
    (h : L < 1) : RealSeriesConverges b := by
  obtain ⟨q, hq0, hLq, hq1⟩ := ENNReal.lt_iff_exists_real_btwn.mp h
  have hqpos : 0 < q := ENNReal.ofReal_pos.mp (bot_le.trans_lt hLq)
  have hqone : q < 1 := by
    exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mp (by simpa using hq1)
  apply nonnegative_series_of_eventual_contraction b hb q hqpos hqone
  have htail := hL.eventually (gt_mem_nhds hLq)
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  obtain ⟨M, hM⟩ := hn
  refine ⟨max N M, fun n hn => ?_⟩
  have hlt := (ENNReal.ofReal_lt_ofReal_iff hqpos).mp
    (hN n ((le_max_left _ _).trans hn))
  exact (div_le_iff₀ (lt_of_le_of_ne (hb n)
    (Ne.symm (hM n ((le_max_right _ _).trans hn))))).mp hlt.le

/-- At nonzero distance, the ratio of term magnitudes is t times the coefficient ratio. -/
theorem complex_term_ratio (a : ℕ → ℂ) (z : ℂ) (hz : z ≠ 0) (n : ℕ) :
    ‖complexPowerSeriesTerm a 0 z (n+1) / complexPowerSeriesTerm a 0 z n‖ =
      ‖z‖ * ‖a (n+1) / a n‖ := by
  simp only [complexPowerSeriesTerm, Complex.ofReal_zero, sub_zero]
  rw [mul_div_mul_comm, pow_succ, mul_div_cancel_left₀ _ (pow_ne_zero _ hz),
    norm_mul, mul_comm]

end PowerSeriesRatio

open PowerSeriesRatio

theorem complex_powerSeries_ratio_radius (a : ℕ → ℂ) (ℓ : ℝ≥0∞)
    (ha : SequenceEventually (fun n => a n ≠ 0))
    (h : Tendsto (fun n => ENNReal.ofReal ‖a (n+1) / a n‖) atTop (𝓝 ℓ)) :
    complexPowerSeriesRadius a = ℓ⁻¹ := by
  symm
  apply complex_powerSeries_radius_unique a 0 (ℓ⁻¹)
  · intro z hz
    simp only [Complex.ofReal_zero, sub_zero] at hz
    by_cases hzero : z = 0
    · subst z
      exact (complex_powerSeries_center_hasSum a 0).2
    have hterm : SequenceEventually (fun n => complexPowerSeriesTerm a 0 z n ≠ 0) := by
      obtain ⟨N, hN⟩ := ha
      exact ⟨N, fun n hn => mul_ne_zero (hN n hn) (pow_ne_zero _ (by simpa using hzero))⟩
    have hlim : Tendsto (fun n => ENNReal.ofReal
        (‖complexPowerSeriesTerm a 0 z (n+1)‖ / ‖complexPowerSeriesTerm a 0 z n‖))
        atTop (𝓝 (ENNReal.ofReal ‖z‖ * ℓ)) := by
      simpa only [← norm_div, complex_term_ratio a z hzero,
        ENNReal.ofReal_mul (norm_nonneg z)] using
        (ENNReal.Tendsto.const_mul h (Or.inr ENNReal.ofReal_ne_top) :
          Tendsto (fun n => ENNReal.ofReal ‖z‖ * ENNReal.ofReal ‖a (n+1) / a n‖)
            atTop (𝓝 (ENNReal.ofReal ‖z‖ * ℓ)))
    exact contraction_of_limit _ (fun n => norm_nonneg _)
      (by obtain ⟨N, hN⟩ := hterm; exact ⟨N, fun n hn => norm_ne_zero_iff.mpr (hN n hn)⟩)
      _ hlim (PowerSeriesRadius.scaled_growth_lt_one hz)
  · intro z hz
    simp only [Complex.ofReal_zero, sub_zero] at hz
    have hzero : z ≠ 0 := by
      intro hzero
      simp [hzero] at hz
    apply complex_ratio_divergence (complexPowerSeriesTerm a 0 z)
    · obtain ⟨N, hN⟩ := ha
      exact ⟨N, fun n hn => mul_ne_zero (hN n hn) (pow_ne_zero _ (by simpa using hzero))⟩
    · have hlim := (ENNReal.Tendsto.const_mul h (Or.inr ENNReal.ofReal_ne_top) :
          Tendsto (fun n => ENNReal.ofReal ‖z‖ * ENNReal.ofReal ‖a (n+1) / a n‖)
            atTop (𝓝 (ENNReal.ofReal ‖z‖ * ℓ)))
      have htail := hlim.eventually
        (lt_mem_nhds (PowerSeriesRadius.one_lt_scaled_growth hz))
      apply (sequenceEventually_iff _).mpr
      filter_upwards [htail] with n hn
      rw [← ENNReal.ofReal_mul (norm_nonneg z), ← complex_term_ratio a z hzero] at hn
      exact (ENNReal.one_lt_ofReal.mp hn).le

/-- Embedding real coefficients preserves their original root-limsup radius. -/
theorem real_powerSeries_radius_complex (a : ℕ → ℝ) :
    complexPowerSeriesRadius (fun n => (a n : ℂ)) = realPowerSeriesRadius a := by
  simp only [complexPowerSeriesRadius, realPowerSeriesRadius,
    complexPowerSeriesRootGrowth, realPowerSeriesRootGrowth, Complex.norm_real, Real.norm_eq_abs]

theorem real_powerSeries_ratio_radius (a : ℕ → ℝ) (ℓ : ℝ≥0∞)
    (ha : SequenceEventually (fun n => a n ≠ 0))
    (h : Tendsto (fun n => ENNReal.ofReal |a (n+1) / a n|) atTop (𝓝 ℓ)) :
    realPowerSeriesRadius a = ℓ⁻¹ := by
  rw [← real_powerSeries_radius_complex]
  apply complex_powerSeries_ratio_radius
  · obtain ⟨N, hN⟩ := ha
    exact ⟨N, fun n hn => Complex.ofReal_ne_zero.mpr (hN n hn)⟩
  · simpa only [← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs] using h

theorem complex_powerSeries_inverse_ratio_radius (a : ℕ → ℂ) (r : ℝ≥0∞)
    (ha : SequenceEventually (fun n => a n ≠ 0))
    (h : Tendsto (fun n => ENNReal.ofReal ‖a n / a (n+1)‖) atTop (𝓝 r)) :
    complexPowerSeriesRadius a = r := by
  have hinv : Tendsto (fun n => ENNReal.ofReal ‖a (n+1) / a n‖) atTop (𝓝 (r⁻¹)) := by
    have ht := tendsto_inv_iff.mpr h
    apply ht.congr'
    obtain ⟨N, hN⟩ := ha
    filter_upwards [eventually_ge_atTop N] with n hn
    have hpos : 0 < ‖a n / a (n+1)‖ :=
      norm_pos_iff.mpr (div_ne_zero (hN n hn) (hN (n+1) (by omega)))
    rw [← ENNReal.ofReal_inv_of_pos hpos, ← norm_inv, inv_div]
  simpa only [inv_inv] using complex_powerSeries_ratio_radius a (r⁻¹) ha hinv

theorem real_powerSeries_inverse_ratio_radius (a : ℕ → ℝ) (r : ℝ≥0∞)
    (ha : SequenceEventually (fun n => a n ≠ 0))
    (h : Tendsto (fun n => ENNReal.ofReal |a n / a (n+1)|) atTop (𝓝 r)) :
    realPowerSeriesRadius a = r := by
  rw [← real_powerSeries_radius_complex]
  apply complex_powerSeries_inverse_ratio_radius
  · obtain ⟨N, hN⟩ := ha
    exact ⟨N, fun n hn => Complex.ofReal_ne_zero.mpr (hN n hn)⟩
  · simpa only [← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs] using h

end SingleVariableAnalysis
