import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.WalshBlocks

/-! Independent statements for the small Walsh difference, paper.tex:12686.
The finite function norm is the supremum norm of the source. -/
namespace Specs.ExpandedFA.AP.SmallWalshDifference
open ExpandedFA.AP.Walsh

/-- The exact norm, for every parameter in the source's range. -/
def exactNorm : Prop := ∀ n : ℕ, 2 ≤ n → ‖difference n‖ = 2 / (n : ℝ)

/-- Every point with exactly one nonzero coordinate attains the positive maximum. -/
def singletonExtremizers : Prop := ∀ n : ℕ, 2 ≤ n → ∀ i : Fin (2 * n),
  difference n (fun j => decide (j = i)) = 2 / (n : ℝ)

end Specs.ExpandedFA.AP.SmallWalshDifference
