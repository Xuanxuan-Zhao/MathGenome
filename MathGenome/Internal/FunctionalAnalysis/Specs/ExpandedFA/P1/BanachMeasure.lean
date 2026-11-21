import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BanachCircleIntegration
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BanachRealMeasure
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.NoCountablyAdditiveBanachMeasure

/-! Independent specification of the complete Banach integration and measure
extension corollary, `paper.tex:5334–5342`, label `fa2:p1:banach-measure`.

The three conjuncts are the full propositions defined in the upstream Specs:
* a positive, translation-invariant, norm-one real continuous linear functional
  on all bounded functions on `ℝ / ℤ`, extending the Lebesgue integral on every
  bounded Lebesgue measurable function;
* an extended nonnegative finitely additive function on every subset of `ℝ`,
  translation invariant and equal to Lebesgue measure on every Lebesgue
  measurable set, including sets of infinite measure;
* nonexistence of a translation-invariant countably additive measure on the
  full power set of `ℝ` agreeing with Lebesgue measure.

These are definitions of propositions, with no assumed existence witnesses.
-/

namespace Specs.ExpandedFA.P1.BanachMeasure

/-- All three conclusions of Banach integration and extension of Lebesgue
measure, with no additional hypotheses. -/
def banachMeasureType : Prop :=
  BanachCircleIntegration.banachCircleIntegrationType ∧
  BanachRealMeasure.banachRealMeasureType ∧
  NoCountablyAdditiveBanachMeasure

end Specs.ExpandedFA.P1.BanachMeasure
