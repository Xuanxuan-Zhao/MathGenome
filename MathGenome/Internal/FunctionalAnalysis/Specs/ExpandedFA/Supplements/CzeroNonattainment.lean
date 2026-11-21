import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.SequenceDuals

/-! The concrete example at paper.tex 6365–6374. As in the canonical sequence
spaces, natural coordinate n is manuscript coordinate n+1, so its coefficient
is (1/2)^(n+1). Both real and complex scalars are covered by RCLike. -/
noncomputable section
open Filter
open scoped Topology
universe u
namespace ExpandedFA.Supplements.CzeroNonattainment
open ExpandedFA.P1.C01SequenceSpaces
open ExpandedFA.FunctionSpaces.SequenceDuals

/-- The first N coordinates are one and all later coordinates are zero. -/
def initialOnes (𝕜 : Type u) [RCLike 𝕜] (N : ℕ) : SequenceC0 𝕜 :=
  ∑ n ∈ Finset.range N, c0Coordinate 𝕜 n

namespace Spec

def Nonattainment : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜], ∃ f : SequenceC0 𝕜 →L[𝕜] 𝕜,
    (∀ x, Summable (fun n => ‖(((1 / 2 : ℝ) ^ (n + 1) : ℝ) : 𝕜) * x.val n‖) ∧
      f x = ∑' n, (((1 / 2 : ℝ) ^ (n + 1) : ℝ) : 𝕜) * x.val n) ∧
    ‖f‖ = 1 ∧
    (∀ N, (∀ n, (initialOnes 𝕜 N).val n = if n < N then 1 else 0) ∧
      ‖initialOnes 𝕜 N‖ ≤ 1 ∧
      f (initialOnes 𝕜 N) = ((1 - (1 / 2 : ℝ) ^ N : ℝ) : 𝕜)) ∧
    Tendsto (fun N => f (initialOnes 𝕜 N)) atTop (𝓝 1) ∧
    (∀ x, ‖x‖ ≤ 1 → ‖f x‖ < 1)

end Spec
end ExpandedFA.Supplements.CzeroNonattainment
