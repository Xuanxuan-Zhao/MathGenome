import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Banach
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03OperatorNorm
import Mathlib.Analysis.Normed.Module.Completion

/-!
Independent specification of Theorem `fa2:p1:c02:completion`, paper.tex 425–433.
All norms, topologies, and scalar actions are the given ones. `RCLike` includes
both real and complex scalars. No completeness or nontriviality of E is assumed.

The canonical completion is Mathlib's uniform completion with its normed-space
structure. The theorem also quantifies over arbitrary Banach completions.
A surjective linear isometry is bundled as a `LinearIsometryEquiv`.
Uniqueness of extensions ranges over all bounded linear extensions, without
assuming the desired norm identity of a competing extension.
-/

universe u v w z

namespace ExpandedFA.P1.C02Completion.Spec

def completionEmbeddingType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E], E →ₗᵢ[𝕜] UniformSpace.Completion E

/-- The explicit canonical embedding, preserving the original scalar action. -/
noncomputable def completionEmbeddingValue : completionEmbeddingType :=
  fun _ _ _ _ _ => UniformSpace.Completion.toComplₗᵢ

/-- Density, norm preservation, distance preservation, and injectivity all
refer to the same explicit embedding and canonical completion norm. -/
def CompletionEmbeddingProperties : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E],
    let i := completionEmbeddingValue 𝕜 E
    DenseRange i ∧ (∀ x, ‖i x‖ = ‖x‖) ∧
      (∀ x y, dist (i x) (i y) = dist x y) ∧ Function.Injective i

/-- Completeness of the actual completion, also expressed using the
manuscript's norm-Cauchy / norm-convergence definition of Banach space. -/
def CompletionBanach : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E],
    CompleteSpace (UniformSpace.Completion E) ∧
      ExpandedFA.P1.C01Banach.Spec.IsBanachSpaceValue
        (UniformSpace.Completion E)

/-- The source existence assertion: a Banach space over the same field,
with an explicitly norm-preserving linear isometry of dense range.
The target is in the same universe as the source, including the zero space. -/
def CompletionExists : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E],
    ∃ (F : Type v) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
      CompleteSpace F ∧
        ExpandedFA.P1.C01Banach.Spec.IsBanachSpaceValue F ∧
        ∃ i : E →ₗᵢ[𝕜] F, DenseRange i ∧ ∀ x, ‖i x‖ = ‖x‖



/-- The universal property of a particular dense linear isometric embedding.
Only the target of the operator must be complete. -/
def ExtensionProperty (𝕜 : Type u) (E : Type v) (H : Type w)
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup H]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 H] (i : E →ₗᵢ[𝕜] H) : Prop :=
  ∀ (F : Type z) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (T : E →L[𝕜] F),
    ∃ S : H →L[𝕜] F,
      S.comp i.toContinuousLinearMap = T ∧ ‖S‖ = ‖T‖ ∧
        ∀ S' : H →L[𝕜] F, S'.comp i.toContinuousLinearMap = T → S' = S

/-- Every bounded operator extends with its norm unchanged along any dense
linear isometric embedding, in particular along any Banach completion. -/
def Extension : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (H : Type w)
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup H]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 H]
    (i : E →ₗᵢ[𝕜] H), DenseRange i → ExtensionProperty.{u, v, w, z} 𝕜 E H i

/-- Two Banach completions of the same normed space are uniquely isometrically
isomorphic over that space, including the zero-space case. -/
def Uniqueness : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (H : Type w) (G : Type z)
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup H]
    [NormedAddCommGroup G] [NormedSpace 𝕜 E] [NormedSpace 𝕜 H]
    [NormedSpace 𝕜 G] [CompleteSpace H] [CompleteSpace G]
    (i : E →ₗᵢ[𝕜] H) (j : E →ₗᵢ[𝕜] G), DenseRange i → DenseRange j →
    ∃! U : H ≃ₗᵢ[𝕜] G, ∀ x, U (i x) = j x

/-- The complete original theorem: existence of a Banach completion with its
norm-preserving dense embedding, the norm-preserving extension property for
every Banach target, and uniqueness relative to any other Banach completion.
Completeness is also given in the manuscript's norm-sequence formulation. -/
def IsometricCompletion : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E],
    ∃ (H : Type v) (_ : NormedAddCommGroup H) (_ : NormedSpace 𝕜 H)
      (_ : CompleteSpace H) (i : E →ₗᵢ[𝕜] H),
      ExpandedFA.P1.C01Banach.Spec.IsBanachSpaceValue H ∧
      DenseRange i ∧ (∀ x, ‖i x‖ = ‖x‖) ∧
      ExtensionProperty.{u, v, v, w} 𝕜 E H i ∧
      ∀ (G : Type z) [NormedAddCommGroup G] [NormedSpace 𝕜 G]
        [CompleteSpace G] (j : E →ₗᵢ[𝕜] G), DenseRange j →
          ∃! U : H ≃ₗᵢ[𝕜] G, ∀ x, U (i x) = j x

end ExpandedFA.P1.C02Completion.Spec
