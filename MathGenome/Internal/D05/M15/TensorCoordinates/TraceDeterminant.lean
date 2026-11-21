import MathGenome.Internal.D05.M15.TensorCoordinates
import MathGenome.Internal.Specs.D05.M15.TensorCoordinates.TraceDeterminant

/-! Trace and determinant of tensor endomorphisms over an arbitrary field,
including empty product bases and singular factor maps. -/

namespace D05.M15.TensorCoordinates.TraceDeterminant

open scoped TensorProduct BigOperators Kronecker

/-- Reuse the intrinsic identity already established for the shared tensor map. -/
theorem trace_tensor : Specs.D05.M15.TensorCoordinates.TraceDeterminant.trace_tensor :=
  D05.M15.TensorCoordinates.trace_tensor

/-- Take the diagonal of the previously established Kronecker matrix in
exactly the given product basis. -/
theorem trace_diagonal_sum :
    Specs.D05.M15.TensorCoordinates.TraceDeterminant.trace_diagonal_sum := by
  intro K V W _ _ _ _ _ n m e f S T
  rw [LinearMap.trace_eq_matrix_trace K (e.tensorProduct f),
    D05.M15.TensorCoordinates.kronecker_matrix e f e f S T]
  simp only [Matrix.trace, Matrix.diag, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type]

/-- The upstream determinant proof uses the product matrix and the
Kronecker determinant theorem; it has no nonsingularity assumption. -/
theorem det_tensor : Specs.D05.M15.TensorCoordinates.TraceDeterminant.det_tensor :=
  D05.M15.TensorCoordinates.det_tensor

/-- With a zero factor the tensor space is a subsingleton. Its sole
endomorphism has trace zero and determinant one. -/
theorem zero_dimension :
    Specs.D05.M15.TensorCoordinates.TraceDeterminant.zero_dimension := by
  intro K V W _ _ _ _ _ _ _ S T h
  have hz : Subsingleton V ∨ Subsingleton W := by
    rcases h with h | h
    · exact Or.inl (Module.finrank_zero_iff.mp h)
    · exact Or.inr (Module.finrank_zero_iff.mp h)
  exact (D05.M15.TensorCoordinates.zero_factor S T hz).2

theorem empty_conventions :
    Specs.D05.M15.TensorCoordinates.TraceDeterminant.empty_conventions := by
  intro K _ A a
  exact ⟨Matrix.det_isEmpty, by simp [Matrix.trace], pow_zero a⟩

end D05.M15.TensorCoordinates.TraceDeterminant
