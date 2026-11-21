import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.PowerSeriesRadius
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Analysis.Normed.Group.FunctionSeries

open Filter
open scoped Topology NNReal ENNReal

namespace D12Complex.PowerSeriesRadius

noncomputable abbrev rootLimsup : Specs.D12Complex.Ch02.PowerSeriesRadius.rootLimsup_type :=
  D12Complex.powerSeriesRootLimsup

noncomputable abbrev radius : Specs.D12Complex.Ch02.PowerSeriesRadius.radius_type :=
  D12Complex.powerSeriesRadius

/-- The scalar-series bridge to Mathlib's Cauchy--Hadamard theorem. The norm
of the nth multilinear map is exactly the norm of c n, including n = 0. -/
theorem radius_eq_formal (c : ℕ → ℂ) :
    powerSeriesRadius c = (FormalMultilinearSeries.ofScalars ℂ c).radius := by
  have h := (FormalMultilinearSeries.ofScalars ℂ c).radius_inv_eq_limsup
  have hn (n : ℕ) : ‖FormalMultilinearSeries.ofScalars ℂ c n‖₊ = ‖c n‖₊ := by
    apply NNReal.eq
    exact FormalMultilinearSeries.ofScalars_norm ℂ c n
  simp only [hn] at h
  exact congrArg Inv.inv h.symm |>.trans (inv_inv _)

theorem summable_norm_inside (c : ℕ → ℂ) (a z : ℂ)
    (h : (‖z - a‖₊ : ℝ≥0∞) < powerSeriesRadius c) :
    Summable (fun n => ‖c n * (z - a) ^ n‖) := by
  rw [radius_eq_formal] at h
  have hs := (FormalMultilinearSeries.ofScalars ℂ c).summable_norm_mul_pow h
  simpa only [FormalMultilinearSeries.ofScalars_norm, coe_nnnorm,
    norm_mul, norm_pow] using hs

theorem summable_inside (c : ℕ → ℂ) (a z : ℂ)
    (h : (‖z - a‖₊ : ℝ≥0∞) < powerSeriesRadius c) :
    Summable (fun n => c n * (z - a) ^ n) :=
  (summable_norm_inside c a z h).of_norm

theorem not_tendsto_zero_outside (c : ℕ → ℂ) (a z : ℂ)
    (h : powerSeriesRadius c < (‖z - a‖₊ : ℝ≥0∞)) :
    ¬ Tendsto (fun n => c n * (z - a) ^ n) atTop (𝓝 0) := by
  intro ht
  have ht' : Tendsto
      (fun n => ‖FormalMultilinearSeries.ofScalars ℂ c n‖ * (‖z - a‖₊ : ℝ) ^ n)
      atTop (𝓝 0) := by
    simpa only [FormalMultilinearSeries.ofScalars_norm, coe_nnnorm,
      norm_mul, norm_pow, norm_zero] using ht.norm
  have hb := (FormalMultilinearSeries.ofScalars ℂ c).le_radius_of_tendsto ht'
  rw [← radius_eq_formal] at hb
  exact not_le_of_gt h hb

theorem not_summable_outside (c : ℕ → ℂ) (a z : ℂ)
    (h : powerSeriesRadius c < (‖z - a‖₊ : ℝ≥0∞)) :
    ¬ Summable (fun n => c n * (z - a) ^ n) :=
  fun hs => not_tendsto_zero_outside c a z h hs.tendsto_atTop_zero

theorem not_convergent_partialSums_outside (c : ℕ → ℂ) (a z : ℂ)
    (h : powerSeriesRadius c < (‖z - a‖₊ : ℝ≥0∞)) :
    ¬ ∃ s : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N, c n * (z - a) ^ n)
      atTop (𝓝 s) := by
  rintro ⟨s, hs⟩
  apply not_tendsto_zero_outside c a z h
  have ht := (hs.comp (tendsto_add_atTop_nat 1)).sub hs
  simpa only [Function.comp_apply, Finset.sum_range_succ, add_sub_cancel_left, sub_self] using ht

theorem uniform_closedDisk (c : ℕ → ℂ) (a : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (h : ENNReal.ofReal r < powerSeriesRadius c) :
    Summable (fun n => ‖c n‖ * r ^ n) ∧
    TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, c n * (z - a) ^ n)
      (fun z => ∑' n, c n * (z - a) ^ n) atTop (Metric.closedBall a r) ∧
    TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, ‖c n * (z - a) ^ n‖)
      (fun z => ∑' n, ‖c n * (z - a) ^ n‖) atTop (Metric.closedBall a r) := by
  have hs : Summable (fun n => ‖c n‖ * r ^ n) := by
    rw [radius_eq_formal] at h
    have hs := (FormalMultilinearSeries.ofScalars ℂ c).summable_norm_mul_pow
      (r := r.toNNReal) h
    simpa only [FormalMultilinearSeries.ofScalars_norm, Real.coe_toNNReal r hr] using hs
  have hb (n : ℕ) (z : ℂ) (hz : z ∈ Metric.closedBall a r) :
      ‖c n * (z - a) ^ n‖ ≤ ‖c n‖ * r ^ n := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (by simpa [dist_eq_norm] using hz) n) (norm_nonneg _)
  exact ⟨hs, tendstoUniformlyOn_tsum_nat hs hb,
    tendstoUniformlyOn_tsum_nat hs (by simpa only [norm_norm] using hb)⟩

theorem radius_eq_top_of_eventually_zero (c : ℕ → ℂ)
    (hc : ∀ᶠ n in atTop, c n = 0) : powerSeriesRadius c = ⊤ := by
  rw [radius_eq_formal]
  apply FormalMultilinearSeries.radius_eq_top_of_eventually_eq_zero
  filter_upwards [hc] with n hn
  exact FormalMultilinearSeries.ofScalars_eq_zero_of_scalar_zero ℂ hn

theorem rootLimsup_eq_with_zeroTerm (c : ℕ → ℂ) (b : ℝ≥0∞) :
    powerSeriesRootLimsup c =
      limsup (fun n => if n = 0 then b else
        ((‖c n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop := by
  apply Filter.limsup_congr
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp only [ne_of_gt hn, ite_false]

end D12Complex.PowerSeriesRadius
