import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-! Independent statement of the open mapping clause of
`fa2:p1:fspace-open-graph`, paper.tex:1979–2007.
Completeness is for the translation uniformity in the shared `FSpace`
definition. No local convexity, separability, or normability is assumed. -/

namespace ExpandedFA.P1.FspaceOpenMappingSpec

/-- Every continuous scalar-linear surjection of real or complex F-spaces
is an open map, including the zero-space cases. -/
def OpenMapping : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F],
    FSpace 𝕜 E → FSpace 𝕜 F →
      ∀ T : E →ₗ[𝕜] F, Continuous T → Function.Surjective T → IsOpenMap T

end ExpandedFA.P1.FspaceOpenMappingSpec
