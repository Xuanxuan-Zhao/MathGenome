import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.FspaceOpenMapping

/-! Independent statements for `fa2:p1:fspace-open-graph`, paper.tex:1979–2007.
The spaces have their given topologies and complete translation uniformities.
No local convexity or normability is assumed. -/

namespace ExpandedFA.P1.FspaceOpenGraphSpec

/-- The open mapping clause, with precisely the shared F-space hypotheses. -/
def OpenMapping : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F],
    FSpace 𝕜 E → FSpace 𝕜 F →
      ∀ T : E →ₗ[𝕜] F, Continuous T → Function.Surjective T → IsOpenMap T

/-- A scalar-linear map of real or complex F-spaces with closed graph is
continuous. The graph is closed in the product of the given topologies. -/
def ClosedGraph : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F],
    FSpace 𝕜 E → FSpace 𝕜 F →
      ∀ T : E →ₗ[𝕜] F, IsClosed {p : E × F | p.2 = T p.1} → Continuous T

end ExpandedFA.P1.FspaceOpenGraphSpec
