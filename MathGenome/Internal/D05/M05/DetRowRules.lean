import MathGenome.Internal.Specs.D05.M05.DetRowRules
import MathGenome.Internal.D05.M05.DetProduct

/-! K05.05.det_row_rules, including the field-valued dependence assertions.
The determinant bridge is proved upstream from the paper's Leibniz sum.
No characteristic or nonzero-scalar restriction is used for the row rules.
-/

namespace D05.M05.DetRowRules

theorem column_swap : D05.Specs.DetRowRules.column_swap := by
  intro R _ n A j k hjk
  rw [DetDefinition.matrix_det_bridge, DetDefinition.matrix_det_bridge,
    Matrix.det_permute']
  simp [Equiv.Perm.sign_swap hjk]

theorem column_scale : D05.Specs.DetRowRules.column_scale := by
  intro R _ n A j a
  rw [DetDefinition.matrix_det_bridge, DetDefinition.matrix_det_bridge]
  have hs : a • (fun i => A i j) = (fun i => a * A i j) := by
    funext i
    rfl
  simpa only [hs, Matrix.updateCol_eq_self] using
    Matrix.det_updateCol_smul A j a (fun i => A i j)

theorem column_add_multiple : D05.Specs.DetRowRules.column_add_multiple := by
  intro R _ n A j k hjk a
  rw [DetDefinition.matrix_det_bridge, DetDefinition.matrix_det_bridge]
  exact Matrix.det_updateCol_add_smul_self A hjk a

theorem row_swap : D05.Specs.DetRowRules.row_swap := by
  intro R _ n A i k hik
  have h := column_swap A.transpose i k hik
  change determinant (A.submatrix (Equiv.swap i k) id).transpose =
    -determinant A.transpose at h
  rwa [DetProduct.det_transpose, DetProduct.det_transpose] at h

theorem row_scale : D05.Specs.DetRowRules.row_scale := by
  intro R _ n A i a
  have h := column_scale A.transpose i a
  rw [Matrix.updateCol_transpose] at h
  rwa [DetProduct.det_transpose, DetProduct.det_transpose] at h

theorem row_add_multiple : D05.Specs.DetRowRules.row_add_multiple := by
  intro R _ n A i k hik a
  have h := column_add_multiple A.transpose i k hik a
  rw [Matrix.updateCol_transpose] at h
  rwa [DetProduct.det_transpose, DetProduct.det_transpose] at h

theorem dependent_columns_zero : D05.Specs.DetRowRules.dependent_columns_zero := by
  intro K _ n A hA
  rw [DetDefinition.matrix_det_bridge]
  exact Matrix.det_eq_zero_of_not_linearIndependent_cols hA

theorem dependent_rows_zero : D05.Specs.DetRowRules.dependent_rows_zero := by
  intro K _ n A hA
  have h := dependent_columns_zero A.transpose hA
  rwa [DetProduct.det_transpose] at h

end D05.M05.DetRowRules
