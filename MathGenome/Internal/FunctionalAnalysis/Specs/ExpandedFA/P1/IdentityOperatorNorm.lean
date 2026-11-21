import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03OperatorNorm

/-!
Independent statements of the identity norm boundary cases, paper.tex:642–643.
The identity and norm are the native ones fixed by C03OperatorNorm. `RCLike`
includes both real and complex scalars. No completeness assumption is made.
-/

namespace ExpandedFA.P1.IdentityOperatorNorm.Spec

universe u v

/-- On any nonzero real or complex normed space the identity has norm one. -/
def IdentityNormNontrivial : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Nontrivial E],
    ‖ContinuousLinearMap.id 𝕜 E‖ = 1

/-- On the zero space the identity has norm zero. -/
def IdentityNormSubsingleton : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Subsingleton E],
    ‖ContinuousLinearMap.id 𝕜 E‖ = 0

end ExpandedFA.P1.IdentityOperatorNorm.Spec
