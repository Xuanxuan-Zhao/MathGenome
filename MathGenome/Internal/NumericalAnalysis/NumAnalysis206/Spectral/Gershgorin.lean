import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Spectral.Gershgorin
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

open scoped BigOperators

namespace NumAnalysis206.Gershgorin

/-- W38: every eigenvalue lies in a row disk. -/
theorem row_disks : Specs.NumAnalysis206.Gershgorin.row_disks := by
  intro n A μ hμ
  have hμ' : Module.End.HasEigenvalue (Matrix.toLin' A) μ := by
    rw [Matrix.toLin'_apply']
    exact hμ
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball hμ'
  exact ⟨i, mem_closedBall_iff_norm.mp hi⟩

/-- Transposition preserves the characteristic polynomial and hence eigenvalues. -/
theorem transpose_eigenvalues {n : ℕ} (A : MatrixDefinitions.Mat ℂ n n) (μ : ℂ) :
    Module.End.HasEigenvalue A.transpose.mulVecLin μ ↔
      Module.End.HasEigenvalue A.mulVecLin μ := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly,
    Module.End.hasEigenvalue_iff_isRoot_charpoly,
    Matrix.charpoly_mulVecLin, Matrix.charpoly_mulVecLin, Matrix.charpoly_transpose]

/-- W38: the column disk assertion, with an independently chosen column. -/
theorem column_disks : Specs.NumAnalysis206.Gershgorin.column_disks := by
  intro n A μ hμ
  obtain ⟨k, hk⟩ := row_disks A.transpose μ ((transpose_eigenvalues A μ).mpr hμ)
  exact ⟨k, by simpa only [Matrix.transpose_apply] using hk⟩

/-- There are no eigenvalues in dimension zero. -/
theorem empty_matrix : Specs.NumAnalysis206.Gershgorin.empty_matrix := by
  intro A μ hμ
  obtain ⟨i, _⟩ := row_disks A μ hμ
  exact Fin.elim0 i

end NumAnalysis206.Gershgorin
