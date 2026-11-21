import MathGenome.Internal.Specs.D05.M09.Gershgorin
import MathGenome.Internal.D05.M04.MatrixOfMap
import MathGenome.Internal.D05.M08.EigenRoots
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Analysis.Complex.Basic

/-! Gershgorin disks for complex matrices, including the empty matrix. -/

namespace D05.M09.Gershgorin

/-- The maximal-coordinate eigenvector estimate, in the paper's norm notation. -/
theorem row_disks : Specs.D05.M09.Gershgorin.row_disks := by
  intro n A μ hμ
  have hμ' : Module.End.HasEigenvalue (Matrix.toLin' A) μ := by
    rw [Matrix.toLin'_apply']
    exact hμ
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball (K := ℂ) (n := Fin n) (A := A) (μ := μ) hμ'
  refine ⟨i, ?_⟩
  exact mem_closedBall_iff_norm.mp hi

/-- Equal characteristic polynomials give the transpose bridge over the same field. -/
theorem transpose_eigenvalues : Specs.D05.M09.Gershgorin.transpose_eigenvalues := by
  intro n A μ
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly,
    Module.End.hasEigenvalue_iff_isRoot_charpoly,
    Matrix.charpoly_mulVecLin, Matrix.charpoly_mulVecLin, Matrix.charpoly_transpose]

/-- Apply the row theorem to the transpose; its rows are the original columns. -/
theorem column_disks : Specs.D05.M09.Gershgorin.column_disks := by
  intro n A μ hμ
  obtain ⟨i, hi⟩ := row_disks A.transpose μ ((transpose_eigenvalues A μ).mpr hμ)
  exact ⟨i, by simpa only [Matrix.transpose_apply] using hi⟩

theorem empty_matrix : Specs.D05.M09.Gershgorin.empty_matrix := by
  intro A μ
  exact D05.M09.Eigenspace.no_eigenvalues_on_zero_space A.mulVecLin μ

end D05.M09.Gershgorin
