import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BanachMeasure
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.BanachCircleIntegration
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.BanachRealMeasure
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.NoCountablyAdditiveBanachMeasure

/-! The complete Banach integration and measure extension corollary.

The upstream results provide, respectively, the invariant circle integral,
the real-line extension constructed by unit cells and bounded exhaustion,
and the Vitali obstruction to countable additivity. Their conjunction is
the full corollary `fa2:p1:banach-measure`.
-/

namespace ExpandedFA.P1

/-- Banach integration on all bounded circle functions, the translation-invariant
finitely additive extension of Lebesgue measure to all real sets, and the
impossibility of imposing countable additivity on such an extension. -/
theorem banach_measure : Specs.ExpandedFA.P1.BanachMeasure.banachMeasureType :=
  ⟨banach_circle_integration, banach_real_measure,
    no_countably_additive_banach_measure⟩

end ExpandedFA.P1
