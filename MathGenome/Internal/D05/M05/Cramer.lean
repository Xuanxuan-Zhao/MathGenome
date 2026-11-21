import MathGenome.Internal.Specs.D05.M05.Cramer
import MathGenome.Internal.D05.M01.System
import MathGenome.Internal.D05.M05.DetInvertible
import MathGenome.Internal.D05.M05.DetUniqueness

/-! Cramer's rule, K05.05.cramer. -/

namespace D05.M05.Cramer

open scoped Matrix BigOperators
open D05.M01.SystemSpec (IsSolutionValue)

theorem column_combination : D05.Specs.Cramer.column_combination := by
  intro R _ n A x j
  rw [DetDefinition.matrix_det_bridge, DetDefinition.matrix_det_bridge]
  change (A.updateCol j (fun k => ∑ i, A k i * x i)).det = x j * A.det
  simpa only [smul_eq_mul, mul_comm] using
    Matrix.det_updateCol_sum A j x

theorem replacement_of_solution : D05.Specs.Cramer.replacement_of_solution := by
  intro K _ n A b x hx j
  change A *ᵥ x = b at hx
  rw [← hx]
  exact column_combination A x j

theorem solution_iff_inverse : D05.Specs.Cramer.solution_iff_inverse := by
  intro K _ n A b hA x
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr (by
    rw [← DetDefinition.matrix_det_bridge]
    exact hA)
  change A *ᵥ x = b ↔ x = A⁻¹ *ᵥ b
  constructor
  · intro hx
    rw [← hx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hu,
      Matrix.one_mulVec]
  · intro hx
    rw [hx, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hu, Matrix.one_mulVec]

theorem existsUnique_solution : D05.Specs.Cramer.existsUnique_solution := by
  intro K _ n A b hA
  refine ⟨A⁻¹ *ᵥ b, (solution_iff_inverse A b hA _).mpr rfl, ?_⟩
  intro x hx
  exact (solution_iff_inverse A b hA x).mp hx

theorem cramer_coordinates : D05.Specs.Cramer.cramer_coordinates := by
  intro K _ n A b x hA hx j
  exact (eq_div_iff hA).mpr (replacement_of_solution A b x hx j).symm

theorem inverse_coordinates : D05.Specs.Cramer.inverse_coordinates := by
  intro K _ n A b hA j
  exact cramer_coordinates A b (A⁻¹ *ᵥ b) hA
    ((solution_iff_inverse A b hA _).mpr rfl) j

theorem empty_system : D05.Specs.Cramer.empty_system := by
  intro K _ A b
  refine ⟨DetDefinition.empty_determinant A, 0, ?_, ?_⟩
  · exact D05.M01.System.empty_rows A b 0
  · intro x _
    exact D05.M01.System.empty_vector_unique x 0

theorem singular_examples : D05.Specs.Cramer.singular_examples := by
  intro K _
  dsimp only
  refine ⟨?_, ⟨0, 1, ?_, ?_, ?_⟩, ?_⟩
  · rw [DetDefinition.matrix_det_bridge]
    simp
  · exact Matrix.zero_mulVec 0
  · exact Matrix.zero_mulVec 1
  · intro h
    have := congrFun h (0 : Fin 1)
    exact zero_ne_one this
  · rintro ⟨x, hx⟩
    change (0 : Matrix (Fin 1) (Fin 1) K) *ᵥ x = (fun _ => 1) at hx
    have h := congrFun hx (0 : Fin 1)
    simp only [Matrix.zero_mulVec, Pi.zero_apply] at h
    exact zero_ne_one h

end D05.M05.Cramer
