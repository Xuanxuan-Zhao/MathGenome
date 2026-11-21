import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.IncompleteCompactHull
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Module.Completion

/-! The example `fa2:p1:c24:incomplete-hull`, paper.tex 5145–5156.
Reuse the canonical c₀₀ subspace of ℓ¹ from the earlier instance of this
example. Natural coordinate n is manuscript coordinate n+1; hulls are real
convex hulls, closed in c₀₀ itself. The completion below is the actual
uniform completion of that normed space. -/
noncomputable section
open Filter Set
open scoped Topology ENNReal
universe u
namespace ExpandedFA.P1.C24IncompleteHull
open IncompleteCompactHull

/-- Coordinate-preserving isometric inclusion into the Banach space ℓ¹. -/
def inclusion (𝕜 : Type u) [RCLike 𝕜] :
    C00 𝕜 →ₗᵢ[𝕜] C01SequenceSpaces.SequenceLp 𝕜 1 :=
  (finiteSupportSubmodule 𝕜).subtypeₗᵢ

def limitCoordinate (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) : 𝕜 :=
  weight n • (n + 1 : 𝕜)⁻¹

def completionCoordinates (𝕜 : Type u) [RCLike 𝕜]
    (z : UniformSpace.Completion (C00 𝕜)) : ℕ → 𝕜 :=
  fun n => (inclusion 𝕜).fromCompletion z n

namespace Spec

def ModelIdentification : Prop := IncompleteCompactHull.Spec.ModelIdentification.{u}

def CompactPoints : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    Tendsto (point 𝕜) atTop (𝓝 0) ∧ IsCompact (compactSet 𝕜)

def PartialSums : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    (∀ N, partialCombination 𝕜 N ∈ convexHull ℝ (compactSet 𝕜)) ∧
    CauchySeq (partialCombination 𝕜)

def CompletionLimit : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∃ z : UniformSpace.Completion (C00 𝕜),
      Tendsto (fun N => (partialCombination 𝕜 N : UniformSpace.Completion (C00 𝕜)))
        atTop (𝓝 z) ∧
      (∀ n, completionCoordinates 𝕜 z n = limitCoordinate 𝕜 n) ∧
      (∀ n, completionCoordinates 𝕜 z n ≠ 0) ∧
      (Function.support (completionCoordinates 𝕜 z)).Infinite

def NoConvergentSubsequence : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (φ : ℕ → ℕ), StrictMono φ →
    ∀ x : C00 𝕜, ¬ Tendsto (partialCombination 𝕜 ∘ φ) atTop (𝓝 x)

def IncompleteSpace : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜], ¬ CompleteSpace (C00 𝕜)

def NoncompactHull : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜], ¬ IsCompact (closedHull 𝕜)

end Spec
end ExpandedFA.P1.C24IncompleteHull
