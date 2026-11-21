import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.NullSequenceDisks

/-! Independent specification of `fa2:p2:compact-disk`, paper.tex:9496–9522.
The lift of the original compact set must be compact in the gauge norm.
The algebraic range and gauge identities identify the entire original disk
space, including the zero disk. Scalars may be real or complex. -/
namespace ExpandedFA.Compactness.CompactDiskEmbeddingSpec

universe u v
noncomputable section
open Set Filter
open scoped Topology Pointwise

variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E

/-- A realization of the entire gauge space with a compact lift of K. -/
def CompactDiskRealization (C K : Set E) : Prop :=
  ∃ (G : Type v) (_ : NormedAddCommGroup G) (_ : NormedSpace 𝕜 G)
    (_ : CompleteSpace G) (i : G →L[𝕜] E),
    Function.Injective i ∧ IsCompactOperator i ∧
    i '' Metric.closedBall (0 : G) 1 = C ∧
    LinearMap.range i.toLinearMap = Submodule.span 𝕜 C ∧
    (∀ x : G, ‖x‖ = gauge C (i x)) ∧
    (Submodule.span 𝕜 C : Set E) = ⋃ (n : ℕ) (_ : 1 ≤ n), (n : ℝ) • C ∧
    IsCompact (i ⁻¹' K)

/-- The full compact-disk embedding, with compactness in the stronger norm. -/
def CompactDiskEmbeddingTheorem : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    ∀ K : Set E, IsCompact K →
    ∃ z : ℕ → E, Tendsto z atTop (𝓝 0) ∧
      K ⊆ NullSequenceDisksSpec.ClosedDiskValue (𝕜 := 𝕜) z ∧
      IsCompact (NullSequenceDisksSpec.ClosedDiskValue (𝕜 := 𝕜) z) ∧
      CompactDiskRealization (𝕜 := 𝕜)
        (NullSequenceDisksSpec.ClosedDiskValue (𝕜 := 𝕜) z) K

end
end ExpandedFA.Compactness.CompactDiskEmbeddingSpec
