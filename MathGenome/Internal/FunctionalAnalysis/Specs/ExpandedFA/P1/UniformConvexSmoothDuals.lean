import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.RotundDefinitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.SmoothnessDefinitions

/-! The two dual equivalences in `fa2:p1:uniform-smooth-duality`.
The scalar-linear continuous dual and the given norm are used throughout.
Neither completeness nor nontriviality is assumed. -/
namespace ExpandedFA.P1.UniformConvexSmoothDuals.Spec
universe u v

def ConvexIffDualSmooth : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 E ↔
      SmoothnessDefinitions.Spec.UniformlySmoothValue 𝕜 (E →L[𝕜] 𝕜)

def SmoothIffDualConvex : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    SmoothnessDefinitions.Spec.UniformlySmoothValue 𝕜 E ↔
      C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 (E →L[𝕜] 𝕜)

end ExpandedFA.P1.UniformConvexSmoothDuals.Spec
