import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02HilbertSumComplete
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.HilbertSumStructure
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.HilbertSumSupportDensity

/-!
Proposition `fa2:p1:c02:hilbert-sum-complete` (paper.tex 497–503).
Assemble the proved structure and support/density results for the same
canonical `lp H 2`, without restricting its index type. The inner product
and its compatibility with the fixed norm are already provided by the
upstream direct-sum interface; completeness makes this space Hilbert.
-/

universe u v w

namespace ExpandedFA.P1.C02HilbertSumComplete

/-- The arbitrary-index Hilbert sum is Hilbert, its coordinate projections
and inclusions are contractive, its finite-support vectors are dense, and
each of its vectors has at most countably many nonzero coordinates. -/
theorem completeness_and_density : Spec.CompletenessAndDensity.{u, v, w} := by
  intro I H _ 𝕜 _ _ _
  exact ⟨HilbertSumStructure.completeness,
    fun i => HilbertSumStructure.coordinate_contractive (𝕜 := 𝕜) i,
    fun i => HilbertSumStructure.inclusion_contractive (𝕜 := 𝕜) i,
    HilbertSumSupportDensity.dense_finiteSupport H,
    fun x => HilbertSumSupportDensity.countable_support x⟩

end ExpandedFA.P1.C02HilbertSumComplete
