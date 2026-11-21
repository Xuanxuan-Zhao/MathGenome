import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Conditioning.LinearPerturbation
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Conditioning.Neumann
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
namespace NumAnalysis206.Conditioning

/-- W11: a unique perturbed solution, the absolute error bound for every right-hand
side, and the relative bound when the original right-hand side is nonzero. -/
theorem perturbedLinearSystems : Specs.perturbedLinearSystems := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A D hsmall
  have hcomp : ‖A.symm.toContinuousLinearMap.comp D‖ ≤
      ‖A.symm.toContinuousLinearMap‖ * ‖D‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  obtain ⟨_, B, _, _, _, hB, hBn, _⟩ :=
    operatorInversePerturbation A D (lt_of_le_of_lt hcomp hsmall)
  have hden : 0 < 1 - ‖A.symm.toContinuousLinearMap‖ * ‖D‖ := sub_pos.mpr hsmall
  have hBn' : ‖B.symm.toContinuousLinearMap‖ ≤
      ‖A.symm.toContinuousLinearMap‖ /
        (1 - ‖A.symm.toContinuousLinearMap‖ * ‖D‖) :=
    hBn.trans (div_le_div_of_nonneg_left (norm_nonneg _) hden (sub_le_sub_left hcomp 1))
  refine ⟨B, hB, ?_⟩
  intro b db x hx
  dsimp only
  have hBx : B x = b + D x := by
    have he := congrArg (fun f : X →L[𝕜] Y => f x) hB
    change B x = A x + D x at he
    simpa only [hx] using he
  have herr : B.symm (b + db) - x = B.symm (db - D x) := by
    apply B.injective
    simp only [map_sub, B.apply_symm_apply, hBx]
    abel
  have habs : ‖B.symm (b + db) - x‖ ≤
      (‖A.symm.toContinuousLinearMap‖ /
        (1 - ‖A.symm.toContinuousLinearMap‖ * ‖D‖)) * (‖db‖ + ‖D‖ * ‖x‖) := by
    calc
      ‖B.symm (b + db) - x‖ = ‖B.symm (db - D x)‖ := congrArg norm herr
      _ ≤ ‖B.symm.toContinuousLinearMap‖ * ‖db - D x‖ :=
        B.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ (‖A.symm.toContinuousLinearMap‖ /
          (1 - ‖A.symm.toContinuousLinearMap‖ * ‖D‖)) * (‖db‖ + ‖D‖ * ‖x‖) :=
        mul_le_mul hBn'
          ((norm_sub_le _ _).trans (add_le_add_right (D.le_opNorm x) _))
          (norm_nonneg _) (by positivity)
  refine ⟨?_, habs, ?_⟩
  · intro z
    rw [← hB]
    exact ⟨fun hz => B.injective (hz.trans (B.apply_symm_apply _).symm),
      fun hz => hz ▸ B.apply_symm_apply _⟩
  · intro hb
    have hx0 : x ≠ 0 := by
      intro hzero
      apply hb
      rw [← hx, hzero, map_zero]
    have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
    have hbnd : ‖b‖ ≤ ‖A.toContinuousLinearMap‖ * ‖x‖ := by
      rw [← hx]
      exact A.toContinuousLinearMap.le_opNorm x
    have hAn : 0 < ‖A.toContinuousLinearMap‖ := by
      by_contra hn
      have hn' : ‖A.toContinuousLinearMap‖ = 0 :=
        le_antisymm (le_of_not_gt hn) (norm_nonneg _)
      rw [hn', zero_mul] at hbnd
      exact (not_le_of_gt hbn) hbnd
    have hdb : ‖db‖ / ‖x‖ ≤ (‖db‖ / ‖b‖) * ‖A.toContinuousLinearMap‖ := by
      apply (div_le_iff₀ hxn).mpr
      calc
        ‖db‖ = (‖db‖ / ‖b‖) * ‖b‖ := (div_mul_cancel₀ _ (ne_of_gt hbn)).symm
        _ ≤ (‖db‖ / ‖b‖) * (‖A.toContinuousLinearMap‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left hbnd (by positivity)
        _ = (‖db‖ / ‖b‖ * ‖A.toContinuousLinearMap‖) * ‖x‖ := by ring
    calc
      ‖B.symm (b + db) - x‖ / ‖x‖ ≤
          ((‖A.symm.toContinuousLinearMap‖ /
            (1 - ‖A.symm.toContinuousLinearMap‖ * ‖D‖)) *
              (‖db‖ + ‖D‖ * ‖x‖)) / ‖x‖ :=
        div_le_div_of_nonneg_right habs (norm_nonneg _)
      _ = (‖A.symm.toContinuousLinearMap‖ /
            (1 - ‖A.symm.toContinuousLinearMap‖ * ‖D‖)) * (‖db‖ / ‖x‖ + ‖D‖) := by
        field_simp
      _ ≤ (‖A.symm.toContinuousLinearMap‖ /
            (1 - ‖A.symm.toContinuousLinearMap‖ * ‖D‖)) *
              ((‖db‖ / ‖b‖) * ‖A.toContinuousLinearMap‖ + ‖D‖) :=
        mul_le_mul_of_nonneg_left (add_le_add_left hdb _) (by positivity)
      _ = (‖A.toContinuousLinearMap‖ * ‖A.symm.toContinuousLinearMap‖) *
            (‖D‖ / ‖A.toContinuousLinearMap‖ + ‖db‖ / ‖b‖) /
            (1 - (‖A.toContinuousLinearMap‖ * ‖A.symm.toContinuousLinearMap‖) *
              (‖D‖ / ‖A.toContinuousLinearMap‖)) := by
        field_simp
        ring

end NumAnalysis206.Conditioning
