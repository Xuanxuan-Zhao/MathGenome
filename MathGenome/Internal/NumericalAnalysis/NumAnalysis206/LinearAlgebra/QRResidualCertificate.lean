import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.QRResidualCertificate
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.NearOrthonormalCorrection

namespace NumAnalysis206.QRResidualCertificate
open MatrixDefinitions

/-- W33: correcting the nearly orthonormal factor increases the residual
by at most the correction bound times the norm of the right factor. -/
theorem exists_certificate :
    Specs.NumAnalysis206.QRResidualCertificate.exists_certificate := by
  intro K _ m n A Qhat Rhat hmn ρ η hη0 hη1 hres hdef
  obtain ⟨Qtilde, horth, hcorr⟩ :=
    NearOrthonormalCorrection.exists_correction Qhat hmn η hη0 hη1 hdef
  refine ⟨Qtilde, horth, ?_⟩
  have hnorm : 0 ≤ operatorNorm Rhat := norm_nonneg _
  calc
    operatorNorm (A - Qtilde * Rhat) =
        operatorNorm ((A - Qhat * Rhat) + (Qhat - Qtilde) * Rhat) := by
      rw [Matrix.sub_mul, sub_add_sub_cancel]
    _ ≤ operatorNorm (A - Qhat * Rhat) +
        operatorNorm ((Qhat - Qtilde) * Rhat) := by
      unfold operatorNorm
      rw [map_add, map_add]
      exact norm_add_le _ _
    _ ≤ ρ + operatorNorm (Qhat - Qtilde) * operatorNorm Rhat :=
      add_le_add hres (MatrixData.operatorNorm_mul_le _ _)
    _ ≤ ρ + (η / (1 + Real.sqrt (1 - η))) * operatorNorm Rhat :=
      add_le_add (le_refl ρ) (mul_le_mul_of_nonneg_right hcorr hnorm)

end NumAnalysis206.QRResidualCertificate
