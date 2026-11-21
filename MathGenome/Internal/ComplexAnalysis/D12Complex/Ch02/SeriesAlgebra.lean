import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.SeriesAlgebra
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.PowerSeriesRadius
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Analytic.Uniqueness

open Filter
open scoped Topology NNReal ENNReal

namespace D12Complex.SeriesAlgebra

open PowerSeriesCalculus

/-- Multiplying a Cauchy coefficient by the nth power distributes that power
among the two factors. This is a finite identity, valid even at w = 0. -/
theorem mulCoefficients_mul_pow (c d : ℕ → ℂ) (w : ℂ) (n : ℕ) :
    mulCoefficients c d n * w ^ n =
      ∑ j ∈ Finset.range (n + 1), (c j * w ^ j) * (d (n - j) * w ^ (n - j)) := by
  rw [mulCoefficients, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have h : j + (n - j) = n := Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  calc
    c j * d (n - j) * w ^ n = c j * d (n - j) * (w ^ j * w ^ (n - j)) := by
      rw [← pow_add, h]
    _ = _ := by ring

private theorem summable_norm_add {u v : ℕ → ℂ}
    (hu : Summable (fun n => ‖u n‖)) (hv : Summable (fun n => ‖v n‖)) :
    Summable (fun n => ‖u n + v n‖) :=
  (hu.add hv).of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_add_le _ _)

theorem sum_add : Specs.D12Complex.Ch02.SeriesAlgebra.sum_add_type := by
  intro c d a z hc hd
  have ha := PowerSeriesRadius.summable_norm_inside c a z hc
  have hb := PowerSeriesRadius.summable_norm_inside d a z hd
  constructor
  · simpa only [addCoefficients, add_mul] using summable_norm_add ha hb
  · simpa only [addCoefficients, add_mul, seriesSum] using ha.of_norm.hasSum.add hb.of_norm.hasSum

theorem sum_mul : Specs.D12Complex.Ch02.SeriesAlgebra.sum_mul_type := by
  intro c d a z hc hd
  have ha := PowerSeriesRadius.summable_norm_inside c a z hc
  have hb := PowerSeriesRadius.summable_norm_inside d a z hd
  constructor
  · simpa only [← mulCoefficients_mul_pow] using
      summable_norm_sum_mul_range_of_summable_norm ha hb
  · simpa only [← mulCoefficients_mul_pow, seriesSum] using
      hasSum_sum_range_mul_of_summable_norm ha hb

/-- A summable coefficient majorant controls both the complex series and its
absolute values uniformly on the entire closed disk. -/
private theorem uniform_of_majorant (c : ℕ → ℂ) (a : ℂ) (r : ℝ)
    (hs : Summable (fun n => ‖c n‖ * r ^ n)) :
    AbsoluteUniformOnDisk c a r (seriesSum c a) := by
  have hb (n : ℕ) (z : ℂ) (hz : z ∈ Metric.closedBall a r) :
      ‖c n * (z - a) ^ n‖ ≤ ‖c n‖ * r ^ n := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (by simpa [dist_eq_norm] using hz) n) (norm_nonneg _)
  exact ⟨hs, tendstoUniformlyOn_tsum_nat hs hb,
    tendstoUniformlyOn_tsum_nat hs (by simpa only [norm_norm] using hb)⟩

private theorem closedBall_subset_disk (c : ℕ → ℂ) (a : ℂ) (r : ℝ)
    (h : ENNReal.ofReal r < powerSeriesRadius c) :
    Metric.closedBall a r ⊆ convergenceDisk c a := by
  intro z hz
  apply lt_of_le_of_lt _ h
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  simpa [dist_eq_norm] using hz

private theorem norm_eval_real (c : ℕ → ℂ) (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    ‖c n * (r : ℂ) ^ n‖ = ‖c n‖ * r ^ n := by
  simp [norm_pow, Complex.norm_real, abs_of_nonneg hr]

theorem uniform_add : Specs.D12Complex.Ch02.SeriesAlgebra.uniform_add_type := by
  intro c d a r hr hc hd
  have ha := (PowerSeriesRadius.uniform_closedDisk c a r hr hc).1
  have hb := (PowerSeriesRadius.uniform_closedDisk d a r hr hd).1
  have ha' : Summable (fun n => ‖c n * (r : ℂ) ^ n‖) := by
    simpa only [norm_eval_real c r hr] using ha
  have hb' : Summable (fun n => ‖d n * (r : ℂ) ^ n‖) := by
    simpa only [norm_eval_real d r hr] using hb
  have hs : Summable (fun n => ‖addCoefficients c d n‖ * r ^ n) := by
    apply (summable_norm_add ha' hb').congr
    intro n
    rw [← add_mul]
    exact norm_eval_real (addCoefficients c d) r hr n
  obtain ⟨hm, hu, hn⟩ := uniform_of_majorant (addCoefficients c d) a r hs
  refine ⟨hm, hu.congr_right ?_, hn⟩
  intro z hz
  exact (sum_add c d a z (closedBall_subset_disk c a r hc hz)
    (closedBall_subset_disk d a r hd hz)).2.tsum_eq

theorem uniform_mul : Specs.D12Complex.Ch02.SeriesAlgebra.uniform_mul_type := by
  intro c d a r hr hc hd
  have ha := (PowerSeriesRadius.uniform_closedDisk c a r hr hc).1
  have hb := (PowerSeriesRadius.uniform_closedDisk d a r hr hd).1
  have ha' : Summable (fun n => ‖c n * (r : ℂ) ^ n‖) := by
    simpa only [norm_eval_real c r hr] using ha
  have hb' : Summable (fun n => ‖d n * (r : ℂ) ^ n‖) := by
    simpa only [norm_eval_real d r hr] using hb
  have hs : Summable (fun n => ‖mulCoefficients c d n‖ * r ^ n) := by
    simpa only [← mulCoefficients_mul_pow, norm_eval_real _ r hr] using
      summable_norm_sum_mul_range_of_summable_norm ha' hb'
  obtain ⟨hm, hu, hn⟩ := uniform_of_majorant (mulCoefficients c d) a r hs
  refine ⟨hm, hu.congr_right ?_, hn⟩
  intro z hz
  exact (sum_mul c d a z (closedBall_subset_disk c a r hc hz)
    (closedBall_subset_disk d a r hd hz)).2.tsum_eq

/-- The one-dimensional formal-series uniqueness theorem needs only the given
local HasSum representations; it adds no convergence or smoothness premise. -/
theorem coefficients_unique : Specs.D12Complex.Ch02.SeriesAlgebra.coefficients_unique_type := by
  intro c d a f hc hd
  have hc' : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ c) a := by
    rw [hasFPowerSeriesAt_iff']
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm] using hc
  have hd' : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ d) a := by
    rw [hasFPowerSeriesAt_iff']
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm] using hd
  exact FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
    (hc'.eq_formalMultilinearSeries hd')

end D12Complex.SeriesAlgebra
