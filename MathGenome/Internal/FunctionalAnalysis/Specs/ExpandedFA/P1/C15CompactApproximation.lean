import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15PartialSums
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions

/-! Independent statements for paper.tex:4097–4103, together with the
finite-list convention at 3810–3823. The maps are the original unique ordered
expansion truncations, with compactness and all norms taken in the given norm.
X is only normed. A compact algebraic linear map is realized as a continuous
linear map in the conclusion. Finite rank is finite dimension of the actual
range. Empty compact sets, zero spaces, and empty finite bases are included. -/

open Filter Topology
noncomputable section
universe u v w
namespace ExpandedFA.P1.C15CompactApproximation.Spec

def RawUniformCompactConvergence : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {e : ℕ → E} (h : ExpandedFA.P1.C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) e)
    (K : Set E), IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x ∈ K, ‖ExpandedFA.P1.C15Basis.Spec.rawPartialSum h N x - x‖ < ε

def FiniteUniformCompactConvergence : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {d : ℕ} {e : Fin d → E} (h : ExpandedFA.P1.C15Basis.Spec.IsRawFiniteBasis (𝕜 := 𝕜) e)
    (K : Set E), IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x ∈ K, ‖ExpandedFA.P1.C15Basis.Spec.finitePartialSum h N x - x‖ < ε

def RawCompactOperatorApproximation : Prop :=
  ∀ {𝕜 : Type u} {X : Type v} {E : Type w} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {e : ℕ → E} (h : ExpandedFA.P1.C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) e)
    (T : X →ₗ[𝕜] E),
    ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue T →
      ∃ U : X →L[𝕜] E, U.toLinearMap = T ∧
        ∃ A : ℕ → X →L[𝕜] E,
          (∀ N x, A N x = ExpandedFA.P1.C15Basis.Spec.rawPartialSum h N (T x)) ∧
          (∀ N, FiniteDimensional 𝕜 (A N).toLinearMap.range) ∧
          Tendsto (fun N => ‖A N - U‖) atTop (𝓝 0)

def FiniteCompactOperatorApproximation : Prop :=
  ∀ {𝕜 : Type u} {X : Type v} {E : Type w} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {d : ℕ} {e : Fin d → E} (h : ExpandedFA.P1.C15Basis.Spec.IsRawFiniteBasis (𝕜 := 𝕜) e)
    (T : X →ₗ[𝕜] E),
    ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue T →
      ∃ U : X →L[𝕜] E, U.toLinearMap = T ∧
        ∃ A : ℕ → X →L[𝕜] E,
          (∀ N x, A N x = ExpandedFA.P1.C15Basis.Spec.finitePartialSum h N (T x)) ∧
          (∀ N, FiniteDimensional 𝕜 (A N).toLinearMap.range) ∧
          Tendsto (fun N => ‖A N - U‖) atTop (𝓝 0)

end ExpandedFA.P1.C15CompactApproximation.Spec
