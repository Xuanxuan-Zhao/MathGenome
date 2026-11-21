import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Analysis.Normed.Operator.Basic

/-!
The two norms in Example fa2:p1:c08:incomplete-norms (paper.tex 1630–1644).
Index `j : ℕ` denotes manuscript index `j+1`. The second copy is the range
of the coordinate inclusion ℓ¹ → ℓ∞, with its actual subspace norm and topology.
The linear equivalence below identifies its underlying vector space with ℓ¹;
it does not assert continuity of its inverse.
-/
noncomputable section
open Filter
open scoped Topology ENNReal
universe u
namespace ExpandedFA.P1.C08IncompleteNorms
open C01SequenceSpaces

abbrev L1 (𝕜 : Type u) [RCLike 𝕜] := SequenceLp 𝕜 1

def inclusion (𝕜 : Type u) [RCLike 𝕜] : L1 𝕜 →ₗ[𝕜] SequenceLInfinity 𝕜 :=
  lp.linearMapOfLE 𝕜 (fun _ : ℕ => 𝕜) le_top

/-- Exactly the ℓ¹ sequences, carrying the norm inherited from ℓ∞. -/
abbrev SupL1 (𝕜 : Type u) [RCLike 𝕜] := ↥(inclusion 𝕜).range

/-- Identity on scalar coordinates, between the two normed copies. -/
def identity (𝕜 : Type u) [RCLike 𝕜] : L1 𝕜 ≃ₗ[𝕜] SupL1 𝕜 :=
  LinearEquiv.ofInjective (inclusion 𝕜) (by
    intro x y h
    exact lp.ext (funext fun j => congrArg (fun z : SequenceLInfinity 𝕜 => z j) h))

/-- The first n coordinates are one, including the zero vector at n = 0. -/
def initialOnes (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) : L1 𝕜 :=
  ∑ j ∈ Finset.range n, lp.single 1 j (1 : 𝕜)

/-- Truncations of the manuscript sequence (1/j) indexed here by j+1. -/
def harmonicTruncation (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) : L1 𝕜 :=
  ∑ j ∈ Finset.range n, lp.single 1 j ((j + 1 : 𝕜)⁻¹)

namespace Spec

/-- Norm formulas and underlying-vector-space identification, over both fields. -/
def TwoNorms : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    CompleteSpace (L1 𝕜) ∧
    (∀ x : L1 𝕜, ‖x‖ = ∑' j, ‖x j‖) ∧
    (∀ (x : L1 𝕜) j, (identity 𝕜 x).val j = x j) ∧
    (∀ x : SupL1 𝕜, ‖x‖ = ⨆ j, ‖x.val j‖) ∧
    (∀ (x : SupL1 𝕜) j, (identity 𝕜).symm x j = x.val j)

def BoundedBijection : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∃ T : L1 𝕜 →L[𝕜] SupL1 𝕜,
      T.toLinearMap = (identity 𝕜).toLinearMap ∧ Function.Bijective T ∧ ‖T‖ ≤ 1

def InitialOnesNorms : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (n : ℕ),
    (∀ j, initialOnes 𝕜 n j = if j < n then 1 else 0) ∧
    ‖initialOnes 𝕜 n‖ = n ∧
    ‖identity 𝕜 (initialOnes 𝕜 n)‖ = if n = 0 then 0 else 1

/-- Unbounded as a linear map, and hence discontinuous. -/
def UnboundedInverse : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    (¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ x : SupL1 𝕜,
      ‖(identity 𝕜).symm x‖ ≤ C * ‖x‖) ∧
    ¬ Continuous ((identity 𝕜).symm : SupL1 𝕜 → L1 𝕜)

/-- The specified Cauchy sequence, with its precise coordinate limit, has no
limit in the supremum-norm copy of ℓ¹. -/
def HarmonicTruncations : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    (∀ n j, harmonicTruncation 𝕜 n j = if j < n then (j + 1 : 𝕜)⁻¹ else 0) ∧
    CauchySeq (fun n => identity 𝕜 (harmonicTruncation 𝕜 n)) ∧
    (∀ j, Tendsto (fun n => (identity 𝕜 (harmonicTruncation 𝕜 n)).val j)
      atTop (𝓝 ((j + 1 : 𝕜)⁻¹))) ∧
    (¬ ∃ x : L1 𝕜, ∀ j, x j = (j + 1 : 𝕜)⁻¹) ∧
    ¬ ∃ x : SupL1 𝕜,
      Tendsto (fun n => identity 𝕜 (harmonicTruncation 𝕜 n)) atTop (𝓝 x)

def Incomplete : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜], ¬ CompleteSpace (SupL1 𝕜)

/-- Closedness in the product of the displayed norm topologies. A product
metric with sum norm has this same topology. The inverse is defined everywhere. -/
def ClosedGraph : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    IsClosed (Function.graph ((identity 𝕜).symm : SupL1 𝕜 → L1 𝕜))

end Spec
end ExpandedFA.P1.C08IncompleteNorms
