import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.AlgebraicRankOneTensors
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Nat.Pairing

/-! Independent specification of the flattening assertion, paper.tex:12672–12676.
A natural-number sequence enumerates finite algebraic representations, with zero
padding. The assertions concern trace and operator limits; no completed tensor
product or injectivity of its operator map is used. -/
noncomputable section
namespace ExpandedFA.AP.SummableTensorFlatteningSpec
open AlgebraicRankOneTensorsSpec
open Filter
universe u v
variable {𝕜 : Type u} {X : Type v} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Enumerate the terms of all finite blocks, padding each block with zero. -/
def flattenedPair (l : ℕ → List ((X →L[𝕜] 𝕜) × X)) (j : ℕ) :
    (X →L[𝕜] 𝕜) × X :=
  (l (Nat.unpair j).1).getD (Nat.unpair j).2 (0, 0)

/-- The initial tensor and each summand retain their algebraic representations.
Their single flattened rank-one series is absolutely summable. Both its scalar
trace and its operator are the limits of the finite tensor partial sums. -/
def Flattening (a : Tensor 𝕜 X) (v : ℕ → Tensor 𝕜 X) : Prop :=
  ∃ l : ℕ → List ((X →L[𝕜] 𝕜) × X),
    tensorSum (l 0) = a ∧
    (∀ m, tensorSum (l (m + 1)) = v m) ∧
    Summable (fun m => cost (l m)) ∧
    Summable (fun j => ‖(flattenedPair l j).1‖ * ‖(flattenedPair l j).2‖) ∧
    HasSum (fun j => (flattenedPair l j).1 (flattenedPair l j).2)
      (trace a + ∑' m, trace (v m)) ∧
    HasSum (fun j => (flattenedPair l j).1.smulRight (flattenedPair l j).2)
      (operator a + ∑' m, operator (v m)) ∧
    Tendsto (fun n => trace (a + ∑ m ∈ Finset.range n, v m)) atTop
      (nhds (trace a + ∑' m, trace (v m))) ∧
    Tendsto (fun n => operator (a + ∑ m ∈ Finset.range n, v m)) atTop
      (nhds (operator a + ∑' m, operator (v m)))

namespace Expected
/-- Real and complex Banach spaces, arbitrary initial tensor and summable
projective infima. Indices `m : ℕ` enumerate the paper's `m ≥ 1`. -/
def Statement : Prop := ∀ {𝕜 : Type u} {X : Type v} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  (a : Tensor 𝕜 X) (v : ℕ → Tensor 𝕜 X),
  Summable (fun m => nu (v m)) → Flattening a v
end Expected
end ExpandedFA.AP.SummableTensorFlatteningSpec
