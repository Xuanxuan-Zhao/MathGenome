import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.SinCos
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.LogDerivative
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.RealPowers
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.StandardLimits
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
The three reference quotients are the already proved derivatives at 0, 0,
and 1. To compose the logarithmic quotient with u, its value at zero must
be repaired to 1. This repaired quotient tends to 1 on the full neighborhood
filter. The identity v log(1+u) = (v u) q(u) holds even at u=0; hence its
limit is L without any eventual nonzero hypothesis on u or bound on v.
Continuity of the series exponential then gives the power limit.
-/
noncomputable section
namespace SingleVariableAnalysis
open Filter Set
open scoped Topology

theorem standard_sine_quotient :
    Specs.SingleVariableAnalysis.Ch07.StandardLimits.sineQuotient := by
  change Tendsto (fun h : ℝ => realSeriesSin h / h) (𝓝[≠] 0) (𝓝 1)
  have hs : realSeriesSin 0 = 0 := real_sinCosSeries_zero.1
  have hc : realSeriesCos 0 = 1 := real_sinCosSeries_zero.2
  have hd : HasDerivAt realSeriesSin (realSeriesCos 0) 0 :=
    (real_sinCosSeries_hasDerivAt 0).1
  rw [hc] at hd
  simpa only [zero_add, hs, sub_zero, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero

theorem standard_exponential_quotient :
    Specs.SingleVariableAnalysis.Ch07.StandardLimits.exponentialQuotient := by
  change Tendsto (fun h : ℝ => (realSeriesExp h - 1) / h) (𝓝[≠] 0) (𝓝 1)
  have he : realSeriesExp 0 = 1 := (expSeries_eq_realExp 0).trans Real.exp_zero
  have hd : HasDerivAt realSeriesExp (realSeriesExp 0) 0 := real_expSeries_hasDerivAt 0
  rw [he] at hd
  simpa only [zero_add, he, smul_eq_mul, div_eq_mul_inv, mul_comm]
    using hd.tendsto_slope_zero

namespace StandardLimits

theorem logarithm_quotient_punctured :
    Tendsto (fun h : ℝ => seriesLog (1 + h) / h) (𝓝[≠] 0) (𝓝 1) := by
  have hl : seriesLog 1 = 0 := seriesLog_one
  have hd : HasDerivAt seriesLog (1 / 1) 1 := seriesLog_hasDerivAt 1 zero_lt_one
  norm_num only [div_self one_ne_zero] at hd
  simpa only [hl, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm]
    using hd.tendsto_slope_zero

/-- The logarithmic quotient with its derivative value at the origin. -/
private def logQuotient (h : ℝ) : ℝ := if h = 0 then 1 else seriesLog (1 + h) / h

private theorem logQuotient_tendsto : Tendsto logQuotient (𝓝 0) (𝓝 1) := by
  have hzero : logQuotient 0 = 1 := by simp [logQuotient]
  have hc : ContinuousAt logQuotient 0 := by
    apply continuousAt_iff_punctured_nhds.mpr
    rw [hzero]
    apply logarithm_quotient_punctured.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    simp only [mem_compl_iff, mem_singleton_iff] at hh
    simp [logQuotient, hh]
  simpa only [hzero] using hc.tendsto

private theorem logarithm_factorization (u v : ℝ) :
    v * seriesLog (1 + u) = (v * u) * logQuotient u := by
  by_cases hu : u = 0
  · have hl : seriesLog 1 = 0 := seriesLog_one
    simp [hu, hl]
  · simp only [logQuotient, ite_eq_right hu]
    field_simp

end StandardLimits

theorem standard_logarithm_quotient :
    Specs.SingleVariableAnalysis.Ch07.StandardLimits.logarithmQuotient := by
  exact StandardLimits.logarithm_quotient_punctured.mono_left
    (nhdsWithin_mono 0 (fun h hh => hh.1))

theorem standard_variable_power_limit :
    Specs.SingleVariableAnalysis.Ch07.StandardLimits.variablePowerLimit := by
  intro α l u v L hu _hpos hvu
  have hq := StandardLimits.logQuotient_tendsto.comp hu
  have hexponent : Tendsto (fun t => v t * seriesLog (1 + u t)) l (𝓝 L) := by
    have hm := hvu.mul hq
    simpa only [Function.comp_def, mul_one, ← StandardLimits.logarithm_factorization] using hm
  have hc : ContinuousAt realSeriesExp L := (real_expSeries_hasDerivAt L).continuousAt
  exact hc.tendsto.comp hexponent

theorem standard_power_at_zero :
    Specs.SingleVariableAnalysis.Ch07.StandardLimits.powerAtZero := by
  intro v
  change realSeriesExp (v * seriesLog (1 + 0)) = 1
  have hl : seriesLog 1 = 0 := seriesLog_one
  simp only [add_zero, hl, mul_zero]
  exact (expSeries_eq_realExp 0).trans Real.exp_zero

theorem standard_reciprocal_power_limit :
    Specs.SingleVariableAnalysis.Ch07.StandardLimits.reciprocalPowerLimit := by
  let l := 𝓝[{h : ℝ | h ≠ 0 ∧ 0 < 1 + h}] (0 : ℝ)
  apply standard_variable_power_limit l (fun h => h) (fun h => 1 / h) 1
  · exact tendsto_id.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact hh.2
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (one_div_mul_cancel hh.1).symm

end SingleVariableAnalysis
