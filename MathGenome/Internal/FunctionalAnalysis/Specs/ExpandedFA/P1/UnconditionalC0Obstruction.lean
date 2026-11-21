import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.DualBases
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15SubsetProjections

/-! Independent statements for the c₀ clause of
`fa2:p1:unconditional-reflexivity`, paper.tex 4359–4376.
The c₀ object is the upstream normed subspace of bounded null sequences.
An embedded copy is a closed scalar-linear subspace with a continuous linear
isomorphism from that actual c₀, not merely a family with bounded partial sums.
Natural index zero corresponds to manuscript index one. -/

open Filter Topology
open scoped BigOperators
noncomputable section
universe u v
namespace ExpandedFA.P1.UnconditionalC0Obstruction.Spec
open C01SequenceSpaces C15SubsetProjections.Spec

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def ContainsC0 (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  ∃ S : Submodule 𝕜 E, IsClosed (S : Set E) ∧ Nonempty (SequenceC0 𝕜 ≃L[𝕜] S)

/-- Consecutive disjoint ambient coordinate intervals, with their actual
coefficients, approximate a subsequence with any prescribed positive errors.
The endpoints and the selected unit indices both increase strictly. -/
def C0BlockApproximation : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (b : SchauderBasis 𝕜 E) (T : SequenceC0 𝕜 →L[𝕜] E)
    (ε : ℕ → ℝ), (∀ k, 0 < ε k) →
    ∃ σ p : ℕ → ℕ, StrictMono σ ∧ StrictMono p ∧ p 0 = 0 ∧
      ∀ k, ‖T (c0Unit 𝕜 (σ k)) -
        ∑ i ∈ Finset.Ico (p k) (p (k + 1)),
          b.coord i (T (c0Unit 𝕜 (σ k))) • b i‖ < ε k

def BoundedCompletenessCriterion : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {e : ℕ → E}, C15Unconditional.Spec.IsUnconditionalSchauderBasisValue 𝕜 E e →
      (DualBasisBasicity.Spec.IsBoundedlyComplete (𝕜 := 𝕜) e ↔ ¬ ContainsC0 𝕜 E)

/-- Finite and empty bases are included without extending them by zero vectors. -/
def FiniteBoundedCompletenessCriterion : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {d : ℕ} {e : Fin d → E}, C15Basis.Spec.IsRawFiniteBasis (𝕜 := 𝕜) e →
      (DualBases.Spec.finiteBoundedlyComplete (𝕜 := 𝕜) e ↔ ¬ ContainsC0 𝕜 E)

end ExpandedFA.P1.UnconditionalC0Obstruction.Spec
