import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.RotundDefinitions

/-! Independent statement of the Radon–Riesz clause of `fa2:p1:uc-stability`,
paper.tex:4656–4678. The normed space may be incomplete, and the limit may
be zero. Both scalar fields use the original continuous scalar-linear dual. -/
namespace ExpandedFA.P1.LurRadonRiesz.Spec
universe u v

def LocallyUniformlyConvexRadonRiesz : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    RotundDefinitions.Spec.LocallyUniformlyConvexValue 𝕜 E →
      RotundDefinitions.Spec.RadonRieszValue 𝕜 E

end ExpandedFA.P1.LurRadonRiesz.Spec
