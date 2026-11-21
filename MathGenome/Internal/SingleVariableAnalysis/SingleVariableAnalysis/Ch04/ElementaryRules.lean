import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.IntegerPowers
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.ElementaryDerivatives
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.TrigInverses
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.Tan
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.ElementaryRules

/-!
The real derivative table of K03.04.elementary_rules (paper.tex:733–761).

The integer entries reuse the proved real-increment power rules and their
equivalence with `HasDerivAt`. Every other entry collects an upstream result
for the actual constructed function. In particular, real powers use the
exp/log construction, tangent uses its defining quotient at every point
where cosine is nonzero, and inverse trigonometric functions use the
principal branches certified upstream. Each theorem asserts derivative
existence, independently of the default value of the total function `deriv`.
-/

namespace SingleVariableAnalysis.ElementaryRules

theorem positive_power (n : ℕ) (x : ℝ) (hn : 0 < n) :
    HasDerivAt (fun t : ℝ => t ^ n) ((n : ℝ) * x ^ (n - 1)) x :=
  (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mp
    (incrementDerivative_positive_power n x hn)

theorem zero_power (x : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ (0 : ℕ)) 0 x :=
  (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mp
    (incrementDerivative_zero_power x)

theorem negative_power (n : ℤ) (x : ℝ) (hn : n < 0) (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => t ^ n) ((n : ℝ) * x ^ (n - 1)) x :=
  (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mp
    (incrementDerivative_negative_power n x hn hx)

theorem real_power (α x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t => realPower t α) (α * realPower x (α - 1)) x :=
  realPower_hasDerivAt α x hx

theorem exp (x : ℝ) : HasDerivAt realSeriesExp (realSeriesExp x) x :=
  real_expSeries_hasDerivAt x

theorem log (x : ℝ) (hx : 0 < x) : HasDerivAt seriesLog (1 / x) x :=
  seriesLog_hasDerivAt x hx

theorem sin (x : ℝ) : HasDerivAt realSeriesSin (realSeriesCos x) x :=
  (real_sinCosSeries_hasDerivAt x).1

theorem cos (x : ℝ) : HasDerivAt realSeriesCos (-realSeriesSin x) x :=
  (real_sinCosSeries_hasDerivAt x).2

theorem tan (x : ℝ) (hx : realSeriesCos x ≠ 0) :
    HasDerivAt (fun t => realSeriesSin t / realSeriesCos t)
      (1 / realSeriesCos x ^ 2) x :=
  Tan.hasDerivAt x hx

theorem arcsin (x : ℝ) (hx : |x| < 1) :
    HasDerivAt principalArcsin (1 / Real.sqrt (1 - x ^ 2)) x :=
  TrigInverses.inverse_derivatives.1 x hx

theorem arccos (x : ℝ) (hx : |x| < 1) :
    HasDerivAt principalArccos (-(1 / Real.sqrt (1 - x ^ 2))) x :=
  TrigInverses.inverse_derivatives.2.1 x hx

theorem arctan (x : ℝ) : HasDerivAt principalArctan (1 / (1 + x ^ 2)) x :=
  TrigInverses.inverse_derivatives.2.2 x

end SingleVariableAnalysis.ElementaryRules
