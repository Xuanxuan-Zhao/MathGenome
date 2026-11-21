import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData

/-! The W39 diagonal norm property for every subordinate finite ℓ_p norm.
The finite supremum is in ℝ≥0, so its value for dimension zero is zero. -/
namespace Specs.NumAnalysis206.LpDiagonalNorm
open scoped NNReal BigOperators ENNReal
open _root_.NumAnalysis206.MatrixDefinitions
universe u

def diagonal_norm : Prop :=
  ∀ {K : Type u} [RCLike K] {n : ℕ} (p : ℝ≥0∞) (hp : 1 ≤ p)
    (d : Fin n → K),
    lpOperatorNorm p hp (Matrix.diagonal d) =
      ((Finset.univ.sup fun i => ‖d i‖₊ : ℝ≥0) : ℝ)

end Specs.NumAnalysis206.LpDiagonalNorm
