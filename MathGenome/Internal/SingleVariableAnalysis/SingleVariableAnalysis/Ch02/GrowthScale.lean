import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.BigO
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.RealPowers
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.GrowthScale

/-!
# The logarithmic, power and exponential growth scale

K03.02.growth_scale, paper.tex:465–475. All functions in the statements
use the constructed Chapter 7 representatives and the inequality definition
of little-o from Chapter 2. Positive-base bridges transfer the library
estimates only on a tail where their bases are positive.

Proof provenance: `Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics`
proves `isLittleO_rpow_exp_pos_mul_atTop` for every real exponent and
positive exponential rate, comparing with a larger integer power.
`isLittleO_log_rpow_rpow_atTop` proves the logarithmic estimate by the
logarithm/power comparison and power laws. Their hypotheses include the
source's zero exponents. The general series theory is upstream of these
estimates, as in the source's dependency order.
-/

noncomputable section
namespace SingleVariableAnalysis

open Filter

theorem logPower_littleO_power :
    ∀ m : ℝ, 0 ≤ m → ∀ ε : ℝ, 0 < ε →
      ScalarLittleO atTop (fun x : ℝ => realPower (seriesLog x) m)
        (fun x : ℝ => realPower x ε) := by
  intro m _hm ε hε
  apply (scalarLittleO_iff_isLittleO _ _ _).mpr
  apply (isLittleO_log_rpow_rpow_atTop m hε).congr'
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hlog : 0 < seriesLog x := by
      rw [seriesLog_eq_realLog x hx0]
      exact Real.log_pos hx
    rw [realPower_eq_rpow _ hlog, seriesLog_eq_realLog x hx0]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (realPower_eq_rpow x hx ε).symm

theorem power_littleO_exp :
    ∀ k : ℝ, 0 ≤ k → ∀ c : ℝ, 0 < c →
      ScalarLittleO atTop (fun x : ℝ => realPower x k)
        (fun x : ℝ => realSeriesExp (c * x)) := by
  intro k _hk c hc
  apply (scalarLittleO_iff_isLittleO _ _ _).mpr
  apply (isLittleO_rpow_exp_pos_mul_atTop k hc).congr'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (realPower_eq_rpow x hx k).symm
  · exact Eventually.of_forall fun x => (expSeries_eq_realExp (c * x)).symm

end SingleVariableAnalysis
