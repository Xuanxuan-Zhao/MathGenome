import MathGenome.Internal.Specs.D05.M09.DiagonalDominance
import MathGenome.Internal.D05.M09.Gershgorin
import MathGenome.Internal.D05.M05.DetInvertible
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-! Strict row and column diagonal dominance, including real scalar descent,
the non-strict counterexample, and the empty case. -/

namespace D05.M09.DiagonalDominance

open D05.M05

private theorem no_zero_eigenvalue_of_det_ne_zero
    {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (hA : determinant A ≠ 0) : ¬ Module.End.HasEigenvalue A.mulVecLin 0 := by
  have hinj : Function.Injective A.mulVecLin :=
    ((DetInvertible.bijective_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA)).1
  rw [Module.End.hasEigenvalue_iff, Module.End.eigenspace_zero]
  exact not_not.mpr (LinearMap.ker_eq_bot.mpr hinj)

theorem complex_row_disks_exclude_zero :
    Specs.D05.M09.DiagonalDominance.complex_row_disks_exclude_zero := by
  intro n A hA i
  simpa only [zero_sub, norm_neg] using not_le.mpr (hA i)

theorem complex_column_disks_exclude_zero :
    Specs.D05.M09.DiagonalDominance.complex_column_disks_exclude_zero := by
  intro n A hA i
  simpa only [zero_sub, norm_neg] using not_le.mpr (hA i)

theorem complex_row : Specs.D05.M09.DiagonalDominance.complex_row := by
  intro n A hA
  have hzero : ¬ Module.End.HasEigenvalue A.mulVecLin 0 := by
    intro h
    obtain ⟨i, hi⟩ := Gershgorin.row_disks A 0 h
    exact complex_row_disks_exclude_zero A hA i hi
  have hdet : determinant A ≠ 0 := by
    rw [DetDefinition.matrix_det_bridge]
    exact det_ne_zero_of_sum_row_lt_diag hA
  exact ⟨hzero, hdet, (DetInvertible.field_inverse_iff_det_ne_zero A).mpr hdet⟩

theorem complex_column : Specs.D05.M09.DiagonalDominance.complex_column := by
  intro n A hA
  have hzero : ¬ Module.End.HasEigenvalue A.mulVecLin 0 := by
    intro h
    obtain ⟨i, hi⟩ := Gershgorin.column_disks A 0 h
    exact complex_column_disks_exclude_zero A hA i hi
  have hdet : determinant A ≠ 0 := by
    rw [DetDefinition.matrix_det_bridge]
    exact det_ne_zero_of_sum_col_lt_diag hA
  exact ⟨hzero, hdet, (DetInvertible.field_inverse_iff_det_ne_zero A).mpr hdet⟩

theorem real_complex_determinant :
    Specs.D05.M09.DiagonalDominance.real_complex_determinant := by
  intro n A
  have heq : determinant (A.map (fun x => (x : ℂ))) = ((determinant A : ℝ) : ℂ) := by
    rw [DetDefinition.matrix_det_bridge, DetDefinition.matrix_det_bridge]
    exact (Complex.ofRealHom.map_det A).symm
  refine ⟨heq, ?_⟩
  rw [heq]
  simp

theorem real_row : Specs.D05.M09.DiagonalDominance.real_row := by
  intro n A hA
  have hc := complex_row (A.map (fun x => (x : ℂ))) (by
    simpa only [Matrix.map_apply, Complex.norm_real] using hA)
  have hdet : determinant A ≠ 0 := (real_complex_determinant A).2.mp hc.2.1
  exact ⟨no_zero_eigenvalue_of_det_ne_zero A hdet, hdet,
    (DetInvertible.field_inverse_iff_det_ne_zero A).mpr hdet⟩

theorem real_column : Specs.D05.M09.DiagonalDominance.real_column := by
  intro n A hA
  have hc := complex_column (A.map (fun x => (x : ℂ))) (by
    simpa only [Matrix.map_apply, Complex.norm_real] using hA)
  have hdet : determinant A ≠ 0 := (real_complex_determinant A).2.mp hc.2.1
  exact ⟨no_zero_eigenvalue_of_det_ne_zero A hdet, hdet,
    (DetInvertible.field_inverse_iff_det_ne_zero A).mpr hdet⟩

theorem nonstrict_counterexample :
    Specs.D05.M09.DiagonalDominance.nonstrict_counterexample := by
  intro K _
  dsimp only
  have hdet : determinant (Matrix.of (fun (_ _ : Fin 2) => (1 : K))) = 0 := by
    rw [DetDefinition.matrix_det_bridge, Matrix.det_fin_two]
    simp
  refine ⟨?_, hdet, ?_⟩
  · intro i
    fin_cases i <;> simp
  · intro h
    exact ((DetInvertible.field_inverse_iff_det_ne_zero _).mp h) hdet

theorem empty_matrix : Specs.D05.M09.DiagonalDominance.empty_matrix := by
  intro K _ A
  refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i,
    DetDefinition.empty_determinant A, ?_⟩
  exact ⟨1, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

end D05.M09.DiagonalDominance
