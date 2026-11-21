import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.Young
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.RealPowers
import Mathlib.Analysis.MeanInequalities

/-!
Young's inequality, K03.09.holder (paper.tex:2626–2632).

We reuse Mathlib's `Real.young_inequality_of_nonneg`, whose proof applies
weighted arithmetic–geometric mean to u^p and v^q with weights 1/p and
1/q. This differs from the manuscript's derivative-minimum proof but has
the same hypotheses and conclusion, including zero inputs. The bridge
below checks the actual upstream partial power at zero and at positive
bases, so no exp/log value at a nonpositive base is silently used.
-/
namespace SingleVariableAnalysis

theorem young_inequality : Specs.SingleVariableAnalysis.Ch09.Young.youngInequality := by
  intro p q hp _hq hpq u v hu hv
  exact Real.young_inequality_of_nonneg hu hv
    (Real.holderConjugate_iff.mpr ⟨hp, by simpa only [one_div] using hpq⟩)

theorem partialRealPower_eq_rpow_of_nonneg :
    Specs.SingleVariableAnalysis.Ch09.Young.partialRealPowerRpow := by
  intro x α hx hα
  change partialRealPower x α = some (x ^ α)
  rcases hx.eq_or_lt with hzero | hpos
  · subst x
    rw [partialRealPower_zero α hα, Real.zero_rpow hα.ne']
  · rw [partialRealPower_positive x hpos α, realPower_eq_rpow x hpos α]

theorem young_inequality_partialRealPower :
    Specs.SingleVariableAnalysis.Ch09.Young.youngInequalityPartial := by
  intro p q hp hq hpq u v hu hv
  rw [partialRealPower_eq_rpow_of_nonneg u p hu (lt_trans zero_lt_one hp),
    partialRealPower_eq_rpow_of_nonneg v q hv (lt_trans zero_lt_one hq)]
  exact young_inequality p q hp hq hpq u v hu hv

end SingleVariableAnalysis
