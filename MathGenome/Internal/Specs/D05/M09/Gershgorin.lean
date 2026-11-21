import MathGenome.Internal.Specs.D05.M04.MatrixOfMap
import MathGenome.Internal.Specs.D05.M09.Eigenspace
import Mathlib.Analysis.Complex.Norm

/-!
Independent specifications for K05.09.gershgorin, paper.tex:1328–1342.
Matrices act on complex coordinate columns by the canonical `mulVecLin` map,
which is the coordinate linear map of the upstream matrix/map interface.
The complex norm is the absolute value in the source. Erasing `i` from
`Finset.univ` implements the sum over all indices different from `i`.
There is no positive-size, invertibility, or diagonalizability assumption.
-/

namespace Specs.D05.M09.Gershgorin

/-- Every complex eigenvalue belongs to a row Gershgorin disk. -/
def row_disks : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ),
    Module.End.HasEigenvalue A.mulVecLin μ →
      ∃ i : Fin n, ‖μ - A i i‖ ≤ ∑ j ∈ Finset.univ.erase i, ‖A i j‖

/-- Transposition preserves the eigenvalues; no conjugation is taken. -/
def transpose_eigenvalues : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ),
    Module.End.HasEigenvalue A.transpose.mulVecLin μ ↔
      Module.End.HasEigenvalue A.mulVecLin μ

/-- Every complex eigenvalue also belongs to a column Gershgorin disk.
The witnessing column can differ from the witnessing row. -/
def column_disks : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ),
    Module.End.HasEigenvalue A.mulVecLin μ →
      ∃ i : Fin n, ‖μ - A i i‖ ≤ ∑ j ∈ Finset.univ.erase i, ‖A j i‖

/-- The zero-size case has no eigenvalues. -/
def empty_matrix : Prop :=
  ∀ (A : Matrix (Fin 0) (Fin 0) ℂ) (μ : ℂ),
    ¬ Module.End.HasEigenvalue A.mulVecLin μ

end Specs.D05.M09.Gershgorin
