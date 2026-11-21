import MathGenome.Internal.RealAnalysis.D11.Ch03.GlobalClosedOpen
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.BorelEnvelopes

/-! Null F_sigma/G_delta envelopes without a finite-measure hypothesis.
Choose closed/open approximations with errors below 2^(-n), then take
their union/intersection. Each resulting error is bounded by every
corresponding approximation error, so it must vanish. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace D11.Ch03.BorelEnvelopes

open LebesgueMeasures

theorem borel_envelopes : Specs.D11.Ch03.BorelEnvelopes.borel_envelopes := by
  classical
  intro d _ E hE
  have hpos (n : ℕ) : 0 < (2 : ℝ)⁻¹ ^ n := pow_pos (by norm_num) n
  choose K U hK hU hKE hEU hEK hUE using fun n =>
    GlobalClosedOpen.global_closed_open_approximation d E hE ((2 : ℝ)⁻¹ ^ n) (hpos n)
  have hbudget (n : ℕ) : ENNReal.ofReal ((2 : ℝ)⁻¹ ^ n) = (2 : ℝ≥0∞)⁻¹ ^ n := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have hKm (n : ℕ) : MeasurableSet[borel (Point d)] (K n) := by
    rw [← LebesgueMeasures.borel_structure d]
    exact (hK n).measurableSet
  have hUm (n : ℕ) : MeasurableSet[borel (Point d)] (U n) := by
    rw [← LebesgueMeasures.borel_structure d]
    exact (hU n).measurableSet
  refine ⟨⋃ n, K n, ⋂ n, U n, ⟨K, hK, rfl⟩, ⟨U, hU, rfl⟩,
    MeasurableSet.iUnion hKm, MeasurableSet.iInter hUm,
    iUnion_subset hKE, subset_iInter hEU, ?_, ?_⟩
  · by_contra hzero
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt hzero
    have hbound : lebesgue d (E \ ⋃ n, K n) < (2 : ℝ≥0∞)⁻¹ ^ n := by
      rw [← hbudget n]
      exact (measure_mono (sdiff_subset_sdiff_right (subset_iUnion K n))).trans_lt (hEK n)
    exact (hbound.trans hn).false
  · by_contra hzero
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt hzero
    have hbound : lebesgue d ((⋂ n, U n) \ E) < (2 : ℝ≥0∞)⁻¹ ^ n := by
      rw [← hbudget n]
      exact (measure_mono (sdiff_subset_sdiff_left (iInter_subset U n))).trans_lt (hUE n)
    exact (hbound.trans hn).false

end D11.Ch03.BorelEnvelopes
