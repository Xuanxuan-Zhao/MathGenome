import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import Mathlib.Analysis.Normed.Group.Quotient

/-!
The complete theorem `fa2:p1:c14:stability` (paper.tex:2767–2772).
The subspace carries its inherited norm and the quotient its distance norm.
All three reflexivity predicates mean surjectivity of the respective canonical
evaluation map into the continuous scalar-linear bidual. The Banach and
closedness hypotheses are retained, over either real or complex scalars,
without separability or nontriviality restrictions.
-/

namespace ExpandedFA.P1.C14Stability.Spec

universe u v

/-- Closed subspaces and closed quotients of a reflexive Banach space are
reflexive; a Banach space is reflexive exactly when its continuous dual is. -/
def Stability : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (M : Submodule 𝕜 E) (hM : IsClosed (M : Set E)),
    letI : IsClosed (M : Set E) := hM
    (C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
      C04CanonicalMap.Spec.IsReflexiveValue 𝕜 M ∧
      C04CanonicalMap.Spec.IsReflexiveValue 𝕜 (E ⧸ M)) ∧
    (C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E ↔
      C04CanonicalMap.Spec.IsReflexiveValue 𝕜 (E →L[𝕜] 𝕜))

end ExpandedFA.P1.C14Stability.Spec
