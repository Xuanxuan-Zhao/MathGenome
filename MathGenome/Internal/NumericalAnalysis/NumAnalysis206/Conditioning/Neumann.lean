import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Conditioning.Neumann
import Mathlib.Tactic.Linarith

noncomputable section
namespace NumAnalysis206.Conditioning

/-- The geometric series gives the inverse without requiring `‖1‖ = 1`. -/
theorem neumannSeries : Specs.neumannSeries := by
  intro R _ _ h1 E hE
  have hn : ‖-E‖ < 1 := by simpa using hE
  refine ⟨Units.oneSub (-E) hn, by simp, ?_, ?_⟩
  · exact (summable_geometric_of_norm_lt_one hn).hasSum
  · change ‖∑' j : ℕ, (-E) ^ j‖ ≤ _
    have hb := tsum_geometric_le_of_norm_lt_one (-E) hn
    simp only [norm_neg, one_div] at *
    linarith

/-- Factor a perturbed unit and use the Neumann inverse. -/
theorem algebraInversePerturbation : Specs.algebraInversePerturbation := by
  intro R _ _ h1 A D hE
  obtain ⟨U, hU, _, hnorm⟩ := neumannSeries h1 ((↑A⁻¹ : R) * D) hE
  let B := A * U
  have hB : (B : R) = (A : R) + D := by
    simp [B, hU, mul_add, ← mul_assoc]
  refine ⟨B, hB, ?_, ?_⟩
  · calc
      ‖(↑B⁻¹ : R)‖ = ‖(↑U⁻¹ : R) * (↑A⁻¹ : R)‖ := by simp [B]
      _ ≤ ‖(↑U⁻¹ : R)‖ * ‖(↑A⁻¹ : R)‖ := norm_mul_le _ _
      _ ≤ (1 / (1 - ‖(↑A⁻¹ : R) * D‖)) * ‖(↑A⁻¹ : R)‖ :=
        mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      _ = ‖(↑A⁻¹ : R)‖ / (1 - ‖(↑A⁻¹ : R) * D‖) := by
        simp only [div_eq_mul_inv, one_mul]
        exact mul_comm _ _
  · have hcancel : (↑B⁻¹ : R) * ((A : R) + D) = 1 := by rw [← hB]; simp
    have hm := congrArg (fun x : R => x * (↑A⁻¹ : R)) hcancel
    simp only [mul_add, add_mul, mul_assoc, Units.mul_inv, mul_one, one_mul] at hm
    rw [neg_mul, neg_mul]
    rw [← mul_assoc] at hm
    apply eq_neg_iff_add_eq_zero.mpr
    rw [sub_add_eq_add_sub, sub_eq_zero]
    exact hm

/-- The factorization works between different Banach spaces as well. -/
theorem operatorInversePerturbation : Specs.operatorInversePerturbation := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A D E hE
  have h1 : ‖(1 : X →L[𝕜] X)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  obtain ⟨u, hu, hs, hn⟩ := neumannSeries h1 E hE
  let U : X ≃L[𝕜] X := ContinuousLinearEquiv.ofUnit u
  have hU : U.toContinuousLinearMap = ContinuousLinearMap.id 𝕜 X + E := hu
  have hUi : U.symm.toContinuousLinearMap = (↑u⁻¹ : X →L[𝕜] X) := rfl
  let B := U.trans A
  have hB : B.toContinuousLinearMap = A.toContinuousLinearMap + D := by
    ext x
    change A (U x) = A x + D x
    have hx := congrArg (fun f : X →L[𝕜] X => f x) hU
    change U x = x + A.symm (D x) at hx
    rw [hx, map_add, A.apply_symm_apply]
  have hBi : B.symm.toContinuousLinearMap =
      U.symm.toContinuousLinearMap.comp A.symm.toContinuousLinearMap := rfl
  refine ⟨U, B, hU, ?_, ?_, hB, ?_, ?_⟩
  · simpa only [hUi] using hs
  · simpa only [hUi] using hn
  · calc
      ‖B.symm.toContinuousLinearMap‖ =
          ‖U.symm.toContinuousLinearMap.comp A.symm.toContinuousLinearMap‖ := by rw [hBi]
      _ ≤ ‖U.symm.toContinuousLinearMap‖ * ‖A.symm.toContinuousLinearMap‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1 / (1 - ‖E‖)) * ‖A.symm.toContinuousLinearMap‖ :=
        mul_le_mul_of_nonneg_right (by simpa only [hUi] using hn) (norm_nonneg _)
      _ = ‖A.symm.toContinuousLinearMap‖ / (1 - ‖E‖) := by
        simp only [div_eq_mul_inv, one_mul]
        exact mul_comm _ _
  · ext y
    have hx := congrArg (fun f : X →L[𝕜] Y => f (A.symm y)) hB
    change B (A.symm y) = A (A.symm y) + D (A.symm y) at hx
    rw [A.apply_symm_apply] at hx
    have hh := congrArg B.symm hx
    simp only [B.symm_apply_apply, map_add] at hh
    change B.symm y - A.symm y = -(B.symm (D (A.symm y)))
    apply eq_neg_iff_add_eq_zero.mpr
    rw [sub_add_eq_add_sub, sub_eq_zero]
    exact hh.symm

end NumAnalysis206.Conditioning
