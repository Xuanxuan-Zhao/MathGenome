import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C04.InverseStability
import MathGenome.Internal.MultivariableAnalysis.D04.C01.OperatorEstimates
import MathGenome.Internal.MultivariableAnalysis.D04.C01.ContinuousOperations
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
open Set Filter Topology
open scoped BigOperators

namespace D04

/-- Neumann's argument in a complete normed ring. The weak bound on the
identity's norm also permits the zero ring of endomorphisms of `E 0`. -/
private theorem neumann_stability {R : Type*} [NormedRing R] [CompleteSpace R]
    (h_one : ‖(1 : R)‖ ≤ 1) (a : Rˣ) (b : R)
    (h : ‖(↑a⁻¹ : R) * (b - ↑a)‖ < 1) :
    ∃ u : Rˣ, ↑u = b ∧
      HasSum (fun j : ℕ => (-((↑a⁻¹ : R) * (b - ↑a))) ^ j * ↑a⁻¹) (↑u⁻¹ : R) ∧
      ‖(↑u⁻¹ : R)‖ ≤ ‖(↑a⁻¹ : R)‖ / (1 - ‖(↑a⁻¹ : R) * (b - ↑a)‖) ∧
      ‖(↑u⁻¹ : R) - ↑a⁻¹‖ ≤
        ‖(↑a⁻¹ : R)‖ ^ 2 * ‖b - ↑a‖ / (1 - ‖(↑a⁻¹ : R) * (b - ↑a)‖) := by
  let x := -((↑a⁻¹ : R) * (b - ↑a))
  have hx : ‖x‖ < 1 := by simpa [x] using h
  let u := a * Units.oneSub x hx
  have hu : (↑u : R) = b := by
    change (↑a : R) * (1 - x) = b
    have hc : (↑a : R) * (↑a⁻¹ : R) = 1 := a.val_inv
    simp only [x, sub_neg_eq_add, mul_add, mul_one, ← mul_assoc, hc, one_mul]
    abel
  have hs : HasSum (fun j : ℕ => x ^ j * (↑a⁻¹ : R)) (↑u⁻¹ : R) := by
    exact (summable_geometric_of_norm_lt_one hx).hasSum.mul_right _
  have hS : ‖∑' j : ℕ, x ^ j‖ ≤ (1 - ‖x‖)⁻¹ := by
    have hb := tsum_geometric_le_of_norm_lt_one x hx
    linarith
  have hi : ‖(↑u⁻¹ : R)‖ ≤ ‖(↑a⁻¹ : R)‖ / (1 - ‖x‖) := by
    calc
      ‖(↑u⁻¹ : R)‖ = ‖(∑' j : ℕ, x ^ j) * (↑a⁻¹ : R)‖ := rfl
      _ ≤ ‖∑' j : ℕ, x ^ j‖ * ‖(↑a⁻¹ : R)‖ := norm_mul_le _ _
      _ ≤ (1 - ‖x‖)⁻¹ * ‖(↑a⁻¹ : R)‖ := mul_le_mul_of_nonneg_right hS (norm_nonneg _)
      _ = ‖(↑a⁻¹ : R)‖ / (1 - ‖x‖) := by rw [div_eq_mul_inv, mul_comm]
  have hid : (↑u⁻¹ : R) - ↑a⁻¹ = (↑u⁻¹ : R) * (↑a - b) * ↑a⁻¹ := by
    have he := Ring.inverse_sub_inverse (a := (↑u : R)) (b := (↑a : R))
      (iff_of_true u.isUnit a.isUnit)
    rw [Ring.inverse_unit, Ring.inverse_unit, hu] at he
    exact he
  have hd : ‖(↑u⁻¹ : R) - ↑a⁻¹‖ ≤
      ‖(↑a⁻¹ : R)‖ ^ 2 * ‖b - ↑a‖ / (1 - ‖x‖) := by
    calc
      ‖(↑u⁻¹ : R) - ↑a⁻¹‖ = ‖(↑u⁻¹ : R) * (↑a - b) * ↑a⁻¹‖ := congrArg norm hid
      _ ≤ (‖(↑u⁻¹ : R)‖ * ‖(↑a : R) - b‖) * ‖(↑a⁻¹ : R)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (‖(↑a⁻¹ : R)‖ / (1 - ‖x‖) * ‖(↑a : R) - b‖) * ‖(↑a⁻¹ : R)‖ := by
        gcongr
      _ = ‖(↑a⁻¹ : R)‖ ^ 2 * ‖b - ↑a‖ / (1 - ‖x‖) := by rw [norm_sub_rev]; ring
  refine ⟨u, hu, hs, ?_, ?_⟩
  · simpa only [x, norm_neg] using hi
  · simpa only [x, norm_neg] using hd

/-- Quantitative stability on the shared Euclidean spaces, in every dimension. -/
theorem inverse_stability : Specs.D04.C04.InverseStability.inverse_stabilityType := by
  intro n A B q T h
  let F := Module.End.toContinuousLinearMap (𝕜 := ℝ) (E n)
  let a := A.toContinuousLinearEquiv.toUnit
  let b := F B
  have hF (L : E n →ₗ[ℝ] E n) :
      Specs.D04.C01.EuclideanInterfaces.Model.linearOperatorNorm L = ‖F L‖ :=
    linearOperatorNorm_eq_standard (F L)
  have ha : (↑a : E n →L[ℝ] E n) = F A.toLinearMap := rfl
  have hai : (↑a⁻¹ : E n →L[ℝ] E n) = F A.symm.toLinearMap := rfl
  have he : (↑a⁻¹ : E n →L[ℝ] E n) * (b - ↑a) =
      F (A.symm.toLinearMap.comp (B - A.toLinearMap)) := by
    rw [hai, ha, ← map_sub, ← map_mul]
    rfl
  have hq : q = ‖(↑a⁻¹ : E n →L[ℝ] E n) * (b - ↑a)‖ := by
    rw [he]; exact hF _
  obtain ⟨u, hu, hs, hi, hd⟩ := neumann_stability
    (show ‖(1 : E n →L[ℝ] E n)‖ ≤ 1 from ContinuousLinearMap.norm_id_le)
    a b (by rwa [← hq])
  let C := (ContinuousLinearEquiv.ofUnit u).toLinearEquiv
  have hC : C.toLinearMap = B := by
    exact congrArg ContinuousLinearMap.toLinearMap hu
  have hCi : F C.symm.toLinearMap = (↑u⁻¹ : E n →L[ℝ] E n) := rfl
  have hT : F T = -((↑a⁻¹ : E n →L[ℝ] E n) * (b - ↑a)) := by
    rw [he, ← map_neg]
  have hterm (j : ℕ) :
      F ((T ^ j).comp A.symm.toLinearMap) =
        (-((↑a⁻¹ : E n →L[ℝ] E n) * (b - ↑a))) ^ j * ↑a⁻¹ := by
    change F (T ^ j * A.symm.toLinearMap) = _
    rw [map_mul, map_pow, hT, hai]
  have hsum : HasSum (fun j : ℕ => F ((T ^ j).comp A.symm.toLinearMap))
      (F C.symm.toLinearMap) := by
    simpa only [hterm, hCi] using hs
  refine ⟨C, hC, hsum, ?_, ?_, ?_⟩
  · have hl := tendsto_iff_norm_sub_tendsto_zero.mp hsum.tendsto_sum_nat
    simpa only [hF, map_sub, map_sum] using hl
  · simpa only [hF, hCi, ← hai, hq] using hi
  · simpa only [hF, map_sub, hCi, ← hai, ← ha, hq] using hd

/-- Invertibility of a matrix means invertibility on the original Euclidean space. -/
theorem matrix_invertible_iff : Specs.D04.C04.InverseStability.matrix_invertible_iffType := by
  intro n M
  have hm : IsUnit (matrixLinearEquiv n n M) ↔ IsUnit M :=
    Matrix.isUnit_toLin_iff (standardBasis n)
  rw [← hm, Module.End.isUnit_iff]
  constructor
  · intro h
    exact ⟨LinearEquiv.ofBijective _ h, rfl⟩
  · rintro ⟨A, hA⟩
    change A.toLinearMap = matrixLinearEquiv n n M at hA
    rw [← hA]
    exact A.bijective

/-- The usual matrix inverse represents the inverse of the same linear map. -/
theorem matrix_inverse_represents : Specs.D04.C04.InverseStability.matrix_inverse_representsType := by
  intro n M A hA
  change A.toLinearMap = matrixLinearEquiv n n M at hA
  change matrixLinearEquiv n n M⁻¹ = A.symm.toLinearMap
  have hm : IsUnit M := (matrix_invertible_iff M).mpr ⟨A, hA⟩
  have hc : A.toLinearMap.comp (matrixLinearEquiv n n M⁻¹) = LinearMap.id := by
    rw [hA, ← matrix_composition, Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hm)]
    exact (Matrix.toLinAlgEquiv (standardBasis n)).map_one
  apply LinearMap.ext
  intro v
  apply A.injective
  have hv := LinearMap.congr_fun hc v
  simpa using hv

theorem general_linear_open : Specs.D04.C04.InverseStability.general_linear_openType := by
  intro n
  have he : {M : Matrix (Fin n) (Fin n) ℝ | IsUnit M} =
      {M | M.det ≠ 0} := by
    ext M
    exact (Matrix.isUnit_iff_isUnit_det M).trans isUnit_iff_ne_zero
  rw [he]
  exact isOpen_ne.preimage continuous_id.matrix_det

theorem matrix_inversion_continuous :
    Specs.D04.C04.InverseStability.matrix_inversion_continuousType := by
  intro n M hM
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_matrix_inv
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det M).mp hM))

/-- The single empty matrix is the identity and has determinant one. -/
theorem inverse_stability_dimension_zero :
    Specs.D04.C04.InverseStability.inverse_stability_dimension_zeroType := by
  intro M
  have hM : M = 1 := Subsingleton.elim _ _
  refine ⟨hM, ?_, empty_matrix_determinant M, ?_, ?_⟩
  · rw [hM]; exact isUnit_one
  · exact Subsingleton.elim _ _
  · exact linearOperatorNorm_from_zero _

end D04
