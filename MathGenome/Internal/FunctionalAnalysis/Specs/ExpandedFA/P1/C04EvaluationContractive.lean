import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap

/-!
Independent specification of Proposition `fa2:p1:c04:evaluation-contractive`
(paper.tex, lines 789–793). The dual and bidual carry their native operator
norms and topologies. The canonical evaluation is the shared upstream map;
no completeness or nontriviality of the original space is assumed.
-/

namespace ExpandedFA.P1.C04EvaluationContractive.Spec

universe u v

/-- For every vector, evaluation is a continuous scalar-linear functional
on the continuous linear dual. -/
def EvaluationContinuousLinear : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E),
    Continuous (fun f : E →L[𝕜] 𝕜 => f x) ∧
      (∀ f g : E →L[𝕜] 𝕜, (f + g) x = f x + g x) ∧
      (∀ (a : 𝕜) (f : E →L[𝕜] 𝕜), (a • f) x = a • f x)

/-- The canonical map is scalar-linear and continuous into the normed bidual. -/
def CanonicalEvaluationContinuousLinear : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    Continuous (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E) ∧
      (∀ x y : E,
        C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E (x + y) =
          C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E x +
            C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E y) ∧
      (∀ (a : 𝕜) (x : E),
        C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E (a • x) =
          a • C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E x)

/-- The preliminary norm inequality, with no norming-functional hypothesis. -/
def CanonicalEvaluationContractive : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E),
    ‖C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E x‖ ≤ ‖x‖

end ExpandedFA.P1.C04EvaluationContractive.Spec
