import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Dual
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
Independent specification of Definition `fa2:p1:c04:canonical-map`
(paper.tex, lines 783–788). Both duals are continuous scalar-linear duals,
with their native operator norms. No completeness or nontriviality of the
original normed space is assumed.
-/

namespace ExpandedFA.P1.C04CanonicalMap.Spec

universe u v

/-- The evaluation map takes values in the continuous linear bidual. -/
def CanonicalEvaluationType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    E →L[𝕜] ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)

/-- Evaluation in both variables, without complex conjugation. -/
noncomputable def CanonicalEvaluationValue : CanonicalEvaluationType :=
  fun 𝕜 _ _ _ _ => ContinuousLinearMap.apply 𝕜 𝕜

def EvaluationFormula : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : E) (f : E →L[𝕜] 𝕜),
    CanonicalEvaluationValue 𝕜 E x f = f x

def IsReflexiveType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E], Prop

/-- Reflexivity uses this evaluation map, rather than an arbitrary
isomorphism with the bidual. -/
def IsReflexiveValue : IsReflexiveType :=
  fun 𝕜 E _ _ _ => Function.Surjective (CanonicalEvaluationValue 𝕜 E)

def ReflexivityCharacterization : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    IsReflexiveValue 𝕜 E ↔ Function.Surjective (CanonicalEvaluationValue 𝕜 E)

end ExpandedFA.P1.C04CanonicalMap.Spec
