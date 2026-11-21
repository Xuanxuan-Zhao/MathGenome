import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData

/-! W33: a QR residual and orthogonality certificate in the Euclidean
operator norm, for real or complex matrices, including zero dimensions. -/
namespace Specs.NumAnalysis206.QRResidualCertificate
open _root_.NumAnalysis206.MatrixDefinitions
universe u

def exists_certificate : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ}
    (A Qhat : Mat K m n) (Rhat : Mat K n n)
    (_hmn : n ≤ m) (ρ η : ℝ) (_hη0 : 0 ≤ η) (_hη1 : η < 1),
    operatorNorm (A - Qhat * Rhat) ≤ ρ →
    operatorNorm (adjoint Qhat * Qhat - 1) ≤ η →
    ∃ Qtilde : Mat K m n, adjoint Qtilde * Qtilde = 1 ∧
      operatorNorm (A - Qtilde * Rhat) ≤
        ρ + (η / (1 + Real.sqrt (1 - η))) * operatorNorm Rhat

end Specs.NumAnalysis206.QRResidualCertificate
