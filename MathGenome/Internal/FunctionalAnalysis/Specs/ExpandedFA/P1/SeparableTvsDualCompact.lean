import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair

/-!
Independent statement of `fa2:p1:separable-tvs-dual-compact`,
paper.tex:3253–3265.

`WeakDual 𝕜 E` is the continuous scalar-linear dual of the original
topological vector space, equipped with the topology of pointwise evaluation
on E. This definition applies to arbitrary topological vector spaces, without
any norm or local convexity assumption. Metrizability concerns the inherited
topology on the compact subset, including the empty subset.
-/

namespace ExpandedFA.P1.SeparableTvsDualCompactSpec

universe u v

/-- Every weak-star compact subset of the continuous dual of a separable
Hausdorff real or complex TVS is metrizable. -/
def CompactDualMetrizable : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [T2Space E] [TopologicalSpace.SeparableSpace E],
    TVS 𝕜 E → ∀ K : Set (WeakDual 𝕜 E), IsCompact K →
      TopologicalSpace.MetrizableSpace K

end ExpandedFA.P1.SeparableTvsDualCompactSpec
