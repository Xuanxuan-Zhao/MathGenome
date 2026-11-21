import MathGenome.Internal.Specs.D05.M05.DetInvertible
import MathGenome.Internal.D05.M04.InverseMatrix
import MathGenome.Internal.D05.M05.Adjugate
import MathGenome.Internal.D05.M05.DetProduct

/-! The determinant criterion for invertibility, K05.05.det_invertible. -/

noncomputable section

namespace D05.M05.DetInvertible

open D05.M05

theorem adjugate_inverse : D05.Specs.DetInvertible.adjugate_inverse := by
  intro R _ n A u hu
  constructor
  · rw [smul_mul_assoc, Adjugate.adjugate_mul, smul_smul, hu]
    simp
  · rw [mul_smul_comm, Adjugate.mul_adjugate, smul_smul, hu]
    simp

theorem inverse_iff_isUnit_det : D05.Specs.DetInvertible.inverse_iff_isUnit_det := by
  intro R _ n A
  constructor
  · rintro ⟨B, _, hAB⟩
    apply IsUnit.of_mul_eq_one (determinant B)
    rw [← DetProduct.det_mul, hAB, DetDefinition.identity_determinant]
  · rintro ⟨u, hu⟩
    exact ⟨(↑(u⁻¹) : R) • adjugate A, adjugate_inverse A u hu.symm⟩

theorem bijective_iff_isUnit_det : D05.Specs.DetInvertible.bijective_iff_isUnit_det := by
  intro R _ n A
  rw [← D05.M04.InverseMatrix.inverse_iff_bijective A]
  exact inverse_iff_isUnit_det A

theorem inverse_eq_adjugate : D05.Specs.DetInvertible.inverse_eq_adjugate := by
  intro R _ n A _
  rw [Adjugate.matrix_adjugate_bridge, DetDefinition.matrix_det_bridge]
  exact Matrix.inv_def A

theorem det_inverse : D05.Specs.DetInvertible.det_inverse := by
  intro R _ n A _
  rw [DetDefinition.matrix_det_bridge, DetDefinition.matrix_det_bridge]
  exact Matrix.det_nonsing_inv A

theorem field_inverse_iff_det_ne_zero :
    D05.Specs.DetInvertible.field_inverse_iff_det_ne_zero := by
  intro K _ n A
  rw [inverse_iff_isUnit_det, isUnit_iff_ne_zero]

theorem field_det_inverse : D05.Specs.DetInvertible.field_det_inverse := by
  intro K _ n A hA
  rw [det_inverse A (isUnit_iff_ne_zero.mpr hA), Ring.inverse_eq_inv]

end D05.M05.DetInvertible
