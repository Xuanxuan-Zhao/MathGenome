import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.ExpProperties
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.LogConstruction

/-!
# The logarithm as inverse of the factorial-series exponential

K03.07.log_construction, paper.tex:1593–1610. We select a preimage under the
shared series construction. Its positive range and injectivity prove existence,
uniqueness and the inverse identities. Identifying this inverse with `Real.log`
on positive arguments then transfers the canonical logarithm's continuity,
order, algebra and endpoint limits. Mathlib's `Real.log` is itself defined using
the inverse of the exponential order isomorphism (Log/Basic.lean); its properties
here do not depend on the integral representation or derivative of logarithm.
-/

noncomputable section
namespace SingleVariableAnalysis

open Set Filter
open scoped Topology

/-- The inverse of the real factorial-series exponential on positive inputs.
Its totalization outside that range carries no assertions. -/
def seriesLog : ℝ → ℝ := Function.invFun realSeriesExp

theorem seriesLog_unique :
    Specs.SingleVariableAnalysis.Ch07.LogConstruction.uniquePreimage := by
  intro y hy
  obtain ⟨x, _, hx⟩ := real_expSeries_bijOn_positive.surjOn hy
  exact ⟨x, hx, fun z hz => real_expSeries_strictMono.injective (hz.trans hx.symm)⟩

theorem expSeries_seriesLog :
    Specs.SingleVariableAnalysis.Ch07.LogConstruction.expLog := by
  intro y hy
  change realSeriesExp (Function.invFun realSeriesExp y) = y
  obtain ⟨x, _, hx⟩ := real_expSeries_bijOn_positive.surjOn hy
  exact Function.invFun_eq ⟨x, hx⟩

theorem seriesLog_expSeries :
    Specs.SingleVariableAnalysis.Ch07.LogConstruction.logExp := by
  intro x
  exact Function.leftInverse_invFun real_expSeries_strictMono.injective x

theorem seriesLog_eq_realLog (y : ℝ) (hy : 0 < y) :
    seriesLog y = Real.log y := by
  apply real_expSeries_strictMono.injective
  calc
    realSeriesExp (seriesLog y) = y := expSeries_seriesLog y hy
    _ = realSeriesExp (Real.log y) :=
      (expSeries_eq_realExp (Real.log y) |>.trans (Real.exp_log hy)).symm

theorem seriesLog_continuousOn :
    Specs.SingleVariableAnalysis.Ch07.LogConstruction.continuity := by
  change ContinuousOn seriesLog (Ioi 0)
  exact (Real.continuousOn_log.mono (fun _ hy => ne_of_gt hy)).congr
    (fun y hy => seriesLog_eq_realLog y hy)

theorem seriesLog_strictMonoOn :
    Specs.SingleVariableAnalysis.Ch07.LogConstruction.strictIncrease := by
  intro x hx y hy hxy
  change seriesLog x < seriesLog y
  rw [seriesLog_eq_realLog x hx, seriesLog_eq_realLog y hy]
  exact Real.strictMonoOn_log hx hy hxy

theorem seriesLog_one :
    Specs.SingleVariableAnalysis.Ch07.LogConstruction.atOne := by
  change seriesLog 1 = 0
  rw [seriesLog_eq_realLog 1 zero_lt_one, Real.log_one]

theorem seriesLog_mul :
    Specs.SingleVariableAnalysis.Ch07.LogConstruction.product := by
  intro u v hu hv
  change seriesLog (u * v) = seriesLog u + seriesLog v
  rw [seriesLog_eq_realLog (u * v) (mul_pos hu hv),
    seriesLog_eq_realLog u hu, seriesLog_eq_realLog v hv]
  exact Real.log_mul hu.ne' hv.ne'

theorem seriesLog_reciprocal :
    Specs.SingleVariableAnalysis.Ch07.LogConstruction.reciprocal := by
  intro u hu
  change seriesLog (1 / u) = -seriesLog u
  rw [seriesLog_eq_realLog (1 / u) (one_div_pos.mpr hu), seriesLog_eq_realLog u hu,
    one_div, Real.log_inv]

theorem seriesLog_tendsto_atTop :
    Specs.SingleVariableAnalysis.Ch07.LogConstruction.limitAtPosInfinity := by
  change Tendsto seriesLog atTop atTop
  apply Real.tendsto_log_atTop.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  exact (seriesLog_eq_realLog y hy).symm

theorem seriesLog_tendsto_zero_right :
    Specs.SingleVariableAnalysis.Ch07.LogConstruction.limitAtZeroRight := by
  change Tendsto seriesLog (𝓝[>] 0) atBot
  apply Real.tendsto_log_nhdsGT_zero.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (seriesLog_eq_realLog y hy).symm

end SingleVariableAnalysis
