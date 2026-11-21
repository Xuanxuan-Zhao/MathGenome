import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.RealPowers
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.TrigInverses

/-!
Independent specification of K03.04.elementary_rules, paper.tex:733–761.
Every row asserts existence and the value of a real-variable derivative.
The objects are the upstream factorial series, inverse logarithm, exp/log
real powers, and principal inverse branches, rather than new functions.

Positive natural powers and the constant zero power are separate, so the
zero case involves no negative exponent. Negative integer powers allow
either sign of nonzero base. Logarithms and real powers require a positive
base; the inverse sine/cosine formulas require the strict interior domain.
Tangent is represented by its defining quotient, only where cosine is
nonzero, as in the upstream natural-domain tangent specification.
-/

namespace Specs.SingleVariableAnalysis.Ch04.ElementaryRules
open Ch07.ExpConstruction Ch07.LogConstruction Ch07.RealPowers
open Ch07.SinCos Ch07.TrigInverses

def positivePowerDerivative : Prop :=
  ∀ (n : ℕ) (x : ℝ), 0 < n →
    HasDerivAt (fun t : ℝ => t ^ n) ((n : ℝ) * x ^ (n - 1)) x

def zeroPowerDerivative : Prop :=
  ∀ x : ℝ, HasDerivAt (fun t : ℝ => t ^ (0 : ℕ)) 0 x

def negativePowerDerivative : Prop :=
  ∀ (n : ℤ) (x : ℝ), n < 0 → x ≠ 0 →
    HasDerivAt (fun t : ℝ => t ^ n) ((n : ℝ) * x ^ (n - 1)) x

def realPowerDerivative : Prop :=
  ∀ (α x : ℝ), 0 < x →
    HasDerivAt (fun t => realPowerValue t α) (α * realPowerValue x (α - 1)) x

def expDerivative : Prop :=
  ∀ x : ℝ, HasDerivAt realSeriesExpValue (realSeriesExpValue x) x

def logDerivative : Prop :=
  ∀ x : ℝ, 0 < x → HasDerivAt seriesLogValue (1 / x) x

def sinDerivative : Prop :=
  ∀ x : ℝ, HasDerivAt realSeriesSinValue (realSeriesCosValue x) x

def cosDerivative : Prop :=
  ∀ x : ℝ, HasDerivAt realSeriesCosValue (-realSeriesSinValue x) x

def tanDerivative : Prop :=
  ∀ x : ℝ, realSeriesCosValue x ≠ 0 →
    HasDerivAt (fun t => realSeriesSinValue t / realSeriesCosValue t)
      (1 / realSeriesCosValue x ^ 2) x

def arcsinDerivative : Prop :=
  ∀ x : ℝ, |x| < 1 →
    HasDerivAt principalArcsinValue (1 / Real.sqrt (1 - x ^ 2)) x

def arccosDerivative : Prop :=
  ∀ x : ℝ, |x| < 1 →
    HasDerivAt principalArccosValue (-(1 / Real.sqrt (1 - x ^ 2))) x

def arctanDerivative : Prop :=
  ∀ x : ℝ, HasDerivAt principalArctanValue (1 / (1 + x ^ 2)) x

end Specs.SingleVariableAnalysis.Ch04.ElementaryRules
