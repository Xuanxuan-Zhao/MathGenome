import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! Independent specifications for the row and column disk assertions of
`paper.tex`, W38. The algebraic action `mulVecLin` is matrix multiplication
on coordinate columns. No Hermitian, normality, or positive-size assumption
is imposed. The complex norm is the modulus, and `univ.erase i` implements
the sum over all indices other than `i`. -/

open scoped BigOperators

namespace Specs.NumAnalysis206.Gershgorin

def row_disks : Prop :=
  ∀ {n : ℕ} (A : NumAnalysis206.MatrixDefinitions.Mat ℂ n n) (μ : ℂ),
    Module.End.HasEigenvalue A.mulVecLin μ →
      ∃ i : Fin n, ‖μ - A i i‖ ≤ ∑ j ∈ Finset.univ.erase i, ‖A i j‖

def column_disks : Prop :=
  ∀ {n : ℕ} (A : NumAnalysis206.MatrixDefinitions.Mat ℂ n n) (μ : ℂ),
    Module.End.HasEigenvalue A.mulVecLin μ →
      ∃ k : Fin n, ‖μ - A k k‖ ≤ ∑ j ∈ Finset.univ.erase k, ‖A j k‖

def empty_matrix : Prop :=
  ∀ (A : NumAnalysis206.MatrixDefinitions.Mat ℂ 0 0) (μ : ℂ),
    ¬ Module.End.HasEigenvalue A.mulVecLin μ

end Specs.NumAnalysis206.Gershgorin
