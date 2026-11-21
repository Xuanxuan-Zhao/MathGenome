import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BoundedWeakstarTopology

/-! Independent statement of the Banach-only continuous-dual clause of
`fa2:p1:bounded-weak-star` (paper.tex:3320–3321 and 3356–3367).
The domain is the original continuous scalar-linear dual of E. Only its
 topology is replaced by beta; E retains its original complete norm.
No nontriviality or separability hypothesis is imposed. -/

namespace ExpandedFA.P1.BoundedWeakstarDual.Spec

/-- The continuous scalar-linear functionals for beta are exactly evaluations,
and the evaluating vector in the Banach predual is unique. -/
def ContinuousDualIdentification : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] (L : (E →L[𝕜] 𝕜) →ₗ[𝕜] 𝕜),
    @Continuous (E →L[𝕜] 𝕜) 𝕜
      (BoundedWeakstarTopology.Spec.TopologyValue 𝕜 E) inferInstance L ↔
      ∃! x : E, ∀ f : E →L[𝕜] 𝕜, L f = f x

end ExpandedFA.P1.BoundedWeakstarDual.Spec
