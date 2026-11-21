import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02Completion
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStar
import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
The incomplete-space counterexample, paper.tex 3394–3406.
The original norm-continuous scalar-linear dual is formed before changing
its topology. The completion and embedding are the canonical ones from the
accepted completion interface. A point outside the image is arbitrary.
Closed dual balls use the operator norm; closedness uses the accepted weak-star
topology. No completeness or separability of E is assumed in the pointwise
claims. The last statement supplies such a point for every incomplete E.
-/

namespace ExpandedFA.P1.KreinSmulianIncomplete.Spec

universe u v
noncomputable section

/-- Evaluation of the unique continuous extension to the completion. -/
def EvaluationType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E], UniformSpace.Completion E → (E →L[𝕜] 𝕜) → 𝕜

def EvaluationValue : EvaluationType :=
  fun _ _ _ _ _ z f => f.fromCompletion z

def HyperplaneType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E], UniformSpace.Completion E → Set (E →L[𝕜] 𝕜)

def HyperplaneValue : HyperplaneType :=
  fun 𝕜 E _ _ _ z => {f | EvaluationValue 𝕜 E z f = 0}

/-- The specified set really is the kernel of a nonzero scalar-linear form,
indeed a surjective one, with exactly the defining evaluation values. -/
def ProperHyperplane : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (z : UniformSpace.Completion E),
    z ∉ Set.range (C02Completion.Spec.completionEmbeddingValue 𝕜 E) →
    ∃ L : (E →L[𝕜] 𝕜) →ₗ[𝕜] 𝕜,
      (∀ f, L f = EvaluationValue 𝕜 E z f) ∧ Function.Surjective L ∧
      HyperplaneValue 𝕜 E z = (LinearMap.ker L : Set (E →L[𝕜] 𝕜))

/-- Every intersection with a closed dual ball rB is weak-star closed in the
whole dual, which also gives relative closedness in that ball. -/
def BallIntersectionsClosed : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (z : UniformSpace.Completion E) (r : ℝ), 0 < r →
    @IsClosed (E →L[𝕜] 𝕜) (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
      (HyperplaneValue 𝕜 E z ∩ Metric.closedBall 0 r)

/-- The same hyperplane is not closed for the weak-star topology. -/
def NotWeakStarClosed : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (z : UniformSpace.Completion E),
    z ∉ Set.range (C02Completion.Spec.completionEmbeddingValue 𝕜 E) →
    ¬ @IsClosed (E →L[𝕜] 𝕜) (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
      (HyperplaneValue 𝕜 E z)

/-- Existence of the counterexample in every incomplete normed space, with
its actual completion point and hyperplane retained as witnesses. -/
def IncompleteCounterexample : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E], ¬ CompleteSpace E →
    ∃ z : UniformSpace.Completion E,
      z ∉ Set.range (C02Completion.Spec.completionEmbeddingValue 𝕜 E) ∧
      (∃ L : (E →L[𝕜] 𝕜) →ₗ[𝕜] 𝕜,
        (∀ f, L f = EvaluationValue 𝕜 E z f) ∧ Function.Surjective L ∧
        HyperplaneValue 𝕜 E z = (LinearMap.ker L : Set (E →L[𝕜] 𝕜))) ∧
      (∀ r : ℝ, 0 < r →
        @IsClosed (E →L[𝕜] 𝕜) (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
          (HyperplaneValue 𝕜 E z ∩ Metric.closedBall 0 r)) ∧
      ¬ @IsClosed (E →L[𝕜] 𝕜) (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
        (HyperplaneValue 𝕜 E z)

end
end ExpandedFA.P1.KreinSmulianIncomplete.Spec
