import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C13Embedding
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
The sequential-to-compact implication of fa2:p1:eberlein-smulian
(paper.tex 3077–3123). All continuous duals are formed using the original
norm topologies. The hypotheses concern sequences in A, with limits anywhere
in E. In particular E need not be complete and A need not be weakly closed.
-/
namespace ExpandedFA.P1.WeakSequentialRelativeCompact.Spec
universe u v
open Filter
open scoped Topology
noncomputable section

abbrev weakTopology (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : TopologicalSpace E :=
  C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)

/-- Relative sequential compactness, allowing limits outside A. -/
def HasWeaklyConvergentSubsequences (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : Set E) : Prop :=
  ∀ s : ℕ → E, (∀ n, s n ∈ A) →
    ∃ (x : E) (r : ℕ → ℕ), StrictMono r ∧
      Tendsto (s ∘ r) atTop (@nhds E (weakTopology 𝕜 E) x)

def SequentialBoundedness : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : Set E),
    HasWeaklyConvergentSubsequences 𝕜 E A →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ A, ‖x‖ ≤ C

/-- Finite norming tests in the predual, with a uniform factor two. -/
def FiniteNormingTests : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (M : Submodule 𝕜 (X →L[𝕜] 𝕜)) [FiniteDimensional 𝕜 M],
    ∃ F : Finset X, (∀ f ∈ F, ‖f‖ ≤ 1) ∧
      ∀ z ∈ M, z ≠ 0 → ∃ f ∈ F, ‖z‖ < 2 * ‖z f‖

/-- The essential bidual assertion, including incomplete E. -/
def BidualClosureInRange : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : Set E),
    HasWeaklyConvergentSubsequences 𝕜 E A →
      @closure ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
        (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜))
        (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E '' A) ⊆
          Set.range (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E)

def SequentialRelativeCompactness : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : Set E),
    HasWeaklyConvergentSubsequences 𝕜 E A →
      @IsCompact E (weakTopology 𝕜 E)
        (@closure E (weakTopology 𝕜 E) A)

end
end ExpandedFA.P1.WeakSequentialRelativeCompact.Spec
