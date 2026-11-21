import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.RealPowers
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.LogDerivative
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.SinCos
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Chain
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Product
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.ElementaryDerivatives
import Mathlib.Tactic.FieldSimp

/-!
The four formulas of K03.07.elementary_derivatives (paper.tex:1809–1826).
Differentiate the actual upstream exp/log construction of powers, then use
the exponent addition law to identify the power-rule coefficient. For the
trigonometric quotients use the reciprocal and quotient rules. The identity
sin² + cos² = 1 used in the cotangent calculation is transported from
`Real.sin_sq_add_cos_sq` through the proved series identifications.
-/
namespace SingleVariableAnalysis

theorem realPower_hasDerivAt :
    Specs.SingleVariableAnalysis.Ch07.ElementaryDerivatives.powerDerivative := by
  intro α x hx
  change HasDerivAt (fun t => realPower t α) (α * realPower x (α - 1)) x
  have hlog : HasDerivAt (fun t => α * seriesLog t) (α * (1 / x)) x :=
    (seriesLog_hasDerivAt x hx).const_mul α
  have h := (real_expSeries_derivative (α * seriesLog x)).comp x hlog
  have hp : realPower x α = realPower x (α - 1) * x := by
    have h := realPower_add x hx (α - 1) 1
    simpa only [sub_add_cancel, realPower_one_exponent x hx] using h
  change HasDerivAt (fun t => realPower t α)
    (realPower x α * (α * (1 / x))) x at h
  convert h using 1
  rw [hp]
  field_simp [ne_of_gt hx]

theorem positiveBase_hasDerivAt :
    Specs.SingleVariableAnalysis.Ch07.ElementaryDerivatives.exponentialDerivative := by
  intro a _ha x
  change HasDerivAt (fun t => realPower a t) (seriesLog a * realPower a x) x
  have hlin : HasDerivAt (fun t : ℝ => t * seriesLog a) (seriesLog a) x :=
    hasDerivAt_mul_const _
  have h := (real_expSeries_derivative (x * seriesLog a)).comp x hlin
  change HasDerivAt (fun t => realPower a t) (realPower a x * seriesLog a) x at h
  simpa only [mul_comm] using h

theorem secant_hasDerivAt :
    Specs.SingleVariableAnalysis.Ch07.ElementaryDerivatives.secantDerivative := by
  intro x hx
  change HasDerivAt (fun t => 1 / realSeriesCos t)
    ((1 / realSeriesCos x) * (realSeriesSin x / realSeriesCos x)) x
  have hc : HasDerivAt realSeriesCos (-realSeriesSin x) x :=
    (real_sinCosSeries_hasDerivAt x).2
  have h := hc.fun_inv hx
  simp only [neg_neg] at h
  simpa only [one_div, div_eq_mul_inv, one_mul, pow_two, mul_inv_rev, mul_assoc,
    mul_left_comm, mul_comm] using h

theorem cotangent_hasDerivAt :
    Specs.SingleVariableAnalysis.Ch07.ElementaryDerivatives.cotangentDerivative := by
  intro x hx
  change HasDerivAt (fun t => realSeriesCos t / realSeriesSin t)
    (-1 / realSeriesSin x ^ 2) x
  have hs : HasDerivAt realSeriesSin (realSeriesCos x) x :=
    (real_sinCosSeries_hasDerivAt x).1
  have hc : HasDerivAt realSeriesCos (-realSeriesSin x) x :=
    (real_sinCosSeries_hasDerivAt x).2
  have hid : realSeriesSin x ^ 2 + realSeriesCos x ^ 2 = 1 := by
    change Specs.SingleVariableAnalysis.Ch07.SinCos.realSeriesSinValue x ^ 2 +
      Specs.SingleVariableAnalysis.Ch07.SinCos.realSeriesCosValue x ^ 2 = 1
    rw [(sinCosSeries_eq_real x).1, (sinCosSeries_eq_real x).2]
    exact Real.sin_sq_add_cos_sq x
  have hn : -realSeriesSin x * realSeriesSin x -
      realSeriesCos x * realSeriesCos x = -1 := by
    nlinarith only [hid]
  have h : HasDerivAt (fun t => realSeriesCos t / realSeriesSin t)
      ((-realSeriesSin x * realSeriesSin x - realSeriesCos x * realSeriesCos x) /
        realSeriesSin x ^ 2) x := hc.fun_div hs hx
  rw [hn] at h
  exact h

end SingleVariableAnalysis
