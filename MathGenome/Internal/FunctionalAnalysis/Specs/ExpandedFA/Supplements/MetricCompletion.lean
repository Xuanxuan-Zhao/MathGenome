import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.MetricCompletionExtension
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02Completion

/-!
Independent statements for `fa2:p1:metric-completion` (paper.tex 5848–5897).
A surjective isometry is bundled as `IsometryEquiv`. No nonemptiness or
vector-space hypothesis is imposed on the metric completion theorem.
The linear comparison uses the very embedding specified in C02Completion,
with its given norm, distance, and scalar action.
-/

universe u v w z

namespace Specs.ExpandedFA.Supplements.MetricCompletion

/-- Uniqueness over the source for arbitrary complete dense isometric embeddings,
including empty sources and completions in different universes. -/
def Uniqueness : Prop :=
  ∀ (X : Type u) (H : Type v) (G : Type w)
    [MetricSpace X] [MetricSpace H] [MetricSpace G]
    [CompleteSpace H] [CompleteSpace G]
    (i : X → H) (j : X → G),
    Isometry i → DenseRange i → Isometry j → DenseRange j →
      ∃! U : H ≃ᵢ G, ∀ x, U (i x) = j x

/-- The full metric theorem: existence, uniqueness of the comparison isometry,
and unique uniform extension preserving every prescribed Lipschitz bound.
The extension clauses apply to every completion, not just an existence witness. -/
def MetricCompletionTheorem : Prop :=
  MetricCompletionExtension.CompletionExists.{u} ∧
  Uniqueness.{u, v, w} ∧
  MetricCompletionExtension.UniformExtension.{u, v, z} ∧
  MetricCompletionExtension.LipschitzExtension.{u, v, z}

/-- Identify the previously constructed linear completion as a metric completion.
Its actual canonical embedding is dense and isometric, its given metric is
complete, and it has the unique comparison with every metric completion of E.
The other completion need not carry any vector-space structure. -/
def LinearCompletionIdentification : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E],
    let i := ExpandedFA.P1.C02Completion.Spec.completionEmbeddingValue 𝕜 E
    CompleteSpace (UniformSpace.Completion E) ∧ Isometry i ∧ DenseRange i ∧
      ∀ (H : Type w) [MetricSpace H] [CompleteSpace H] (j : E → H),
        Isometry j → DenseRange j →
          ∃! U : UniformSpace.Completion E ≃ᵢ H, ∀ x, U (i x) = j x

end Specs.ExpandedFA.Supplements.MetricCompletion
