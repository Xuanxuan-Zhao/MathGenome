import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData

/-! The correction used in W33 (paper.tex, proof after the QR certificate).
The norm is the Euclidean induced operator norm. Dimensions may be zero. -/
namespace Specs.NumAnalysis206.NearOrthonormalCorrection
open _root_.NumAnalysis206.MatrixDefinitions
universe u

def exists_correction : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (Qhat : Mat K m n)
    (_hmn : n ≤ m) (η : ℝ) (_hη0 : 0 ≤ η) (_hη1 : η < 1),
    operatorNorm (adjoint Qhat * Qhat - 1) ≤ η →
    ∃ Qtilde : Mat K m n, adjoint Qtilde * Qtilde = 1 ∧
      operatorNorm (Qhat - Qtilde) ≤ η / (1 + Real.sqrt (1 - η))

end Specs.NumAnalysis206.NearOrthonormalCorrection
