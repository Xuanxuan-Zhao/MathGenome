import MathGenome.Internal.Specs.D05.M05.Cofactor
import MathGenome.Internal.D05.M05.DetDefinition

/-! Cofactor expansion over commutative rings, with ordered deleted minors. -/

noncomputable section

namespace D05.M05.Cofactor

open scoped BigOperators

def deletedMatrix : D05.Specs.Cofactor.deletedMatrix_type :=
  D05.Specs.Cofactor.deletedMatrix_value

def cofactor : D05.Specs.Cofactor.cofactor_type :=
  D05.Specs.Cofactor.cofactor_value

theorem deletion_indices : D05.Specs.Cofactor.deletion_indices := by
  intro n i
  exact ⟨Fin.strictMono_succAbove i, Fin.range_succAbove i⟩

theorem deletedMatrix_entry : D05.Specs.Cofactor.deletedMatrix_entry := by
  intro R n A i j k l
  rfl

theorem paper_sign : D05.Specs.Cofactor.paper_sign := by
  intro R _ n A i j
  unfold D05.M05.cofactor
  congr 1
  simp only [pow_add, pow_one]
  ring

theorem column_expansion : D05.Specs.Cofactor.column_expansion := by
  intro R _ n A j
  calc
    D05.M05.determinant A = Matrix.det A := DetDefinition.matrix_det_bridge A
    _ = ∑ i, (-1 : R) ^ (i.val + j.val) * A i j *
        Matrix.det (A.submatrix i.succAbove j.succAbove) := Matrix.det_succ_column A j
    _ = ∑ i, A i j * D05.M05.cofactor A i j := by
      apply Finset.sum_congr rfl
      intro i _
      unfold D05.M05.cofactor D05.M05.deletedMatrix
      rw [DetDefinition.matrix_det_bridge]
      ring

theorem row_expansion : D05.Specs.Cofactor.row_expansion := by
  intro R _ n A i
  calc
    D05.M05.determinant A = Matrix.det A := DetDefinition.matrix_det_bridge A
    _ = ∑ j, (-1 : R) ^ (i.val + j.val) * A i j *
        Matrix.det (A.submatrix i.succAbove j.succAbove) := Matrix.det_succ_row A i
    _ = ∑ j, A i j * D05.M05.cofactor A i j := by
      apply Finset.sum_congr rfl
      intro j _
      unfold D05.M05.cofactor D05.M05.deletedMatrix
      rw [DetDefinition.matrix_det_bridge]
      ring

theorem singleton_minor : D05.Specs.Cofactor.singleton_minor := by
  intro R _ A i j
  exact DetDefinition.empty_determinant _

theorem singleton_cofactor : D05.Specs.Cofactor.singleton_cofactor := by
  intro R _ A i j
  unfold D05.M05.cofactor
  rw [singleton_minor A i j]
  simp

theorem singleton_expansion : D05.Specs.Cofactor.singleton_expansion := by
  intro R _ A
  rw [DetDefinition.matrix_det_bridge]
  exact Matrix.det_fin_one A

end D05.M05.Cofactor
