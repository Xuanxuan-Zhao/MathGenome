import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions

/-!
Independent statement of `fa2:p1:compact-hull-frechet`, paper.tex:2140–2143.

The scalar field is real or complex. Convex hulls use the compatible underlying
real vector space, and closure and compactness use the given topology.
`FrechetSpace` supplies local convexity, metrizability (hence Hausdorffness),
and completeness for the translation uniformity of that topology.
No nonemptiness or nontriviality hypothesis is imposed.
-/

namespace ExpandedFA.P1.CompactHullFrechetSpec

/-- The closed real convex hull of a compact subset of a Fréchet space is compact. -/
def CompactHull : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E],
    FrechetSpace 𝕜 E →
      ∀ K : Set E, IsCompact K → IsCompact (closure (convexHull ℝ K))

end ExpandedFA.P1.CompactHullFrechetSpec
