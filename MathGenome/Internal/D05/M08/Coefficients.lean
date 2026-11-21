import MathGenome.Internal.Specs.D05.M08.Coefficients
import MathGenome.Internal.D05.M08.Charpoly
import MathGenome.Internal.D05.M04.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! K05.08.coefficients: trace and determinant coefficients over every field. -/

noncomputable section

namespace D05.M08.Coefficients

/-- Transfer the library coefficient computation to the paper's determinant. -/
theorem matrix_trace_coefficient : Specs.D05.M08.Coefficients.matrix_trace_coefficient := by
  intro K _ n A hn
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [← D05.M08.Charpoly.matrix_det_formula]
  have h : A.charpoly.coeff (n - 1) = -Matrix.trace A := by
    simpa only [Fintype.card_fin, neg_neg] using
      congrArg Neg.neg (Matrix.trace_eq_neg_charpoly_coeff A).symm
  exact ⟨h, h⟩

/-- Polynomial evaluation at zero commutes with determinant; negating all
columns contributes one factor of `-1` for each column, including zero columns. -/
theorem matrix_constant_coefficient : Specs.D05.M08.Coefficients.matrix_constant_coefficient := by
  intro K _ n A
  rw [← D05.M08.Charpoly.matrix_det_formula,
    D05.M05.DetDefinition.matrix_det_bridge,
    D05.M05.DetDefinition.matrix_det_bridge]
  constructor
  · simp [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpoly]
  · simpa using Matrix.det_neg A

/-- Choosing the canonical finite basis transfers the matrix identity to `T`. -/
theorem operator_trace_coefficient : Specs.D05.M08.Coefficients.operator_trace_coefficient := by
  intro K V _ _ _ _ T hn
  let b := Module.finBasis K V
  rw [Specs.D05.M08.Charpoly.charpoly_value,
    ← LinearMap.charpoly_toMatrix T b, LinearMap.trace_eq_matrix_trace K b T]
  have : Nonempty (Fin (Module.finrank K V)) := ⟨⟨0, hn⟩⟩
  simpa only [Fintype.card_fin, neg_neg] using
    congrArg Neg.neg (Matrix.trace_eq_neg_charpoly_coeff (LinearMap.toMatrix b b T)).symm

/-- The constant coefficient uses every finite dimension, including zero. -/
theorem operator_constant_coefficient : Specs.D05.M08.Coefficients.operator_constant_coefficient := by
  intro K V _ _ _ _ T
  let b := Module.finBasis K V
  rw [Specs.D05.M08.Charpoly.charpoly_value,
    ← LinearMap.charpoly_toMatrix T b, ← LinearMap.det_toMatrix b]
  have h := Matrix.det_eq_sign_charpoly_coeff (LinearMap.toMatrix b b T)
  simpa only [Fintype.card_fin, ← mul_assoc, ← pow_add, (Even.add_self (Module.finrank K V)).neg_one_pow, one_mul] using congrArg
      (fun x : K => (-1 : K) ^ Module.finrank K V * x) h.symm

end D05.M08.Coefficients
