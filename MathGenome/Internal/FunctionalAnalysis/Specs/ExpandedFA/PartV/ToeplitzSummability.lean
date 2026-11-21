import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.SequenceDuals

/-! Independent statements for `fa2:p5:toeplitz-summability`.
Natural coordinate `k` denotes the manuscript coordinate `k+1`.
Rows may have infinite support. A finite real bound on all row absolute sums
expresses the finiteness of their supremum. -/

noncomputable section
open Filter
open scoped Topology
universe u

namespace ExpandedFA.PartV.ToeplitzSummability

open ExpandedFA.FunctionSpaces.SequenceDuals

def matrixTransform {𝕜 : Type u} [RCLike 𝕜]
    (A : ℕ → ℕ → 𝕜) (x : ℕ → 𝕜) : ℕ → 𝕜 :=
  fun n => ∑' k, A n k * x k

def Regular {𝕜 : Type u} [RCLike 𝕜] (A : ℕ → ℕ → 𝕜) : Prop :=
  ∀ (x : ℕ → 𝕜) (l : 𝕜), Tendsto x atTop (𝓝 l) →
    Tendsto (matrixTransform A x) atTop (𝓝 l)

def ToeplitzConditions {𝕜 : Type u} [RCLike 𝕜] (A : ℕ → ℕ → 𝕜) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧ ∀ n, (∑' k, ‖A n k‖) ≤ C) ∧
  (∀ k, Tendsto (fun n => A n k) atTop (𝓝 0)) ∧
  Tendsto (fun n => ∑' k, A n k) atTop (𝓝 1)

namespace Spec

/-- Infinite rows act by absolutely convergent series on every convergent
scalar sequence. -/
def AbsoluteRows : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (A : ℕ → ℕ → 𝕜),
    (∀ n, Summable (fun k => ‖A n k‖)) →
    ∀ (x : ℕ → 𝕜) (l : 𝕜), Tendsto x atTop (𝓝 l) →
      ∀ n, Summable (fun k => ‖A n k * x k‖) ∧
        HasSum (fun k => A n k * x k) (matrixTransform A x n)

/-- The row operator on c has exactly its ℓ¹ norm; in particular no support
restriction or loss of a constant occurs in the necessary bound. -/
def RowFunctional : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (a : ℕ → 𝕜),
    Summable (fun k => ‖a k‖) →
    ∃ L : SequenceConvergent 𝕜 →L[𝕜] 𝕜,
      (∀ x, L x = ∑' k, a k * x.val k) ∧ ‖L‖ = ∑' k, ‖a k‖

/-- The full Silverman–Toeplitz equivalence, over both manuscript fields. -/
def SilvermanToeplitz : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (A : ℕ → ℕ → 𝕜),
    (∀ n, Summable (fun k => ‖A n k‖)) →
      (Regular A ↔ ToeplitzConditions A)

end Spec
end ExpandedFA.PartV.ToeplitzSummability
