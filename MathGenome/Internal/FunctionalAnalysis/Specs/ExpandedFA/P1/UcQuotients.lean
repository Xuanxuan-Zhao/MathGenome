import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14UniformConvexity
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02QuotientNorm

/-!
Independent statement of the quotient clause of `fa2:p1:uc-stability`,
paper.tex:4656–4674. The norm is exactly the distance quotient norm on the
algebraic quotient by the given closed scalar-linear subspace. The shared
closed-unit-ball predicate includes the zero space. No completeness or
existence of minimum-norm representatives is assumed.
-/
namespace ExpandedFA.P1.UcQuotients.Spec

universe u v

/-- Uniform convexity passes to every closed-subspace distance quotient,
over either of the manuscript's scalar fields. -/
def UniformlyConvexQuotient : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (M : Submodule 𝕜 E) (hM : IsClosed (M : Set E)),
    C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 E →
      letI : IsClosed (M : Set E) := hM
      C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 (E ⧸ M)

end ExpandedFA.P1.UcQuotients.Spec
