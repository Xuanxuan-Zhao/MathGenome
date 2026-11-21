import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Conditioning.Residual
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Conditioning.Errors
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-! Linear residual bounds and the attained, unique b-only backward certificate. -/
open scoped NNReal ENNReal
noncomputable section
universe u v w
namespace NumAnalysis206.Conditioning

def linearResidual : Specs.NumAnalysis206.Conditioning.Residual.linearResidualType :=
  @Specs.NumAnalysis206.Conditioning.Residual.linearResidual

def linearConditionNumber : Specs.NumAnalysis206.Conditioning.Residual.linearConditionNumberType :=
  @Specs.NumAnalysis206.Conditioning.Residual.linearConditionNumber

def rightHandSideSolution : Specs.NumAnalysis206.Conditioning.Residual.rightHandSideSolutionType :=
  @Specs.NumAnalysis206.Conditioning.Residual.rightHandSideSolution

theorem residual_absolute_bound :
    Specs.NumAnalysis206.Conditioning.Residual.residual_absolute_boundStatement := by
  intro 𝕜 _ X Y _ _ _ _ A x xhat b hAx
  have hid : A.symm (b - A xhat) = x - xhat := by
    rw [← hAx, map_sub, A.symm_apply_apply, A.symm_apply_apply]
  calc
    ‖xhat - x‖ = ‖A.symm (b - A xhat)‖ := by rw [hid, norm_sub_rev]
    _ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖b - A xhat‖ :=
      A.symm.toContinuousLinearMap.le_opNorm _

theorem residual_relative_bound :
    Specs.NumAnalysis206.Conditioning.Residual.residual_relative_boundStatement := by
  intro 𝕜 _ X Y _ _ _ _ A x xhat b hAx hb
  have hx : x ≠ 0 := by
    intro h
    apply hb
    simpa [h] using hAx.symm
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hbound := residual_absolute_bound A x xhat b hAx
  have hdata : ‖b‖ ≤ ‖A.toContinuousLinearMap‖ * ‖x‖ := by
    rw [← hAx]
    exact A.toContinuousLinearMap.le_opNorm x
  change ‖xhat - x‖ / ‖x‖ ≤
    (‖A.toContinuousLinearMap‖ * ‖A.symm.toContinuousLinearMap‖) *
      ‖Specs.NumAnalysis206.Conditioning.Residual.linearResidual A b xhat‖ / ‖b‖
  apply (div_le_div_iff₀ hxn hbn).mpr
  calc
    ‖xhat - x‖ * ‖b‖ ≤
        (‖A.symm.toContinuousLinearMap‖ *
          ‖Specs.NumAnalysis206.Conditioning.Residual.linearResidual A b xhat‖) * ‖b‖ :=
      mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
    _ ≤ (‖A.symm.toContinuousLinearMap‖ *
          ‖Specs.NumAnalysis206.Conditioning.Residual.linearResidual A b xhat‖) *
          (‖A.toContinuousLinearMap‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left hdata (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

theorem rightHandSide_feasible_iff :
    Specs.NumAnalysis206.Conditioning.Residual.rightHandSide_feasible_iffStatement := by
  intro 𝕜 _ X Y _ _ _ _ A b xhat δb
  change (δb ∈ Set.univ ∧ ∃ h : b + δb ∈ Set.univ,
    A.symm (b + δb) = xhat) ↔ δb = -(b - A xhat)
  constructor
  · rintro ⟨_, _, h⟩
    have heq : b + δb = A xhat := by
      simpa using congrArg A h
    rw [neg_sub]
    exact (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using heq))
  · intro h
    refine ⟨Set.mem_univ _, Set.mem_univ _, ?_⟩
    rw [h]
    have heq : b + -(b - A xhat) = A xhat := by abel
    rw [heq, A.symm_apply_apply]

theorem rightHandSide_backwardError_eq :
    Specs.NumAnalysis206.Conditioning.Residual.rightHandSide_backwardError_eqStatement := by
  intro 𝕜 _ X Y _ _ _ _ A b xhat
  apply le_antisymm
  · have h := (rightHandSide_feasible_iff A b xhat
        (-Specs.NumAnalysis206.Conditioning.Residual.linearResidual A b xhat)).mpr rfl
    have hle := backwardError_le_of_feasible
      (Specs.NumAnalysis206.Conditioning.Residual.rightHandSideSolution A)
      ⟨b, Set.mem_univ b⟩ xhat Set.univ normwiseSize _ h
    simpa [Specs.NumAnalysis206.Conditioning.Errors.normwiseBackwardError,
      normwiseSize, Specs.NumAnalysis206.Conditioning.Errors.normwiseSize] using hle
  · apply le_sInf
    rintro r ⟨δb, hfeas, hsize⟩
    have hδ := (rightHandSide_feasible_iff A b xhat δb).mp hfeas
    subst δb
    change (‖Specs.NumAnalysis206.Conditioning.Residual.linearResidual A b xhat‖₊ : ℝ≥0∞) ≤ r
    simpa [Specs.NumAnalysis206.Conditioning.Errors.normwiseSize] using le_of_eq hsize

theorem rightHandSide_backwardError_attained :
    Specs.NumAnalysis206.Conditioning.Residual.rightHandSide_backwardError_attainedStatement := by
  intro 𝕜 _ X Y _ _ _ _ A b xhat
  refine ⟨⟨(rightHandSide_feasible_iff A b xhat _).mpr rfl, ?_⟩, ?_⟩
  · simp [Specs.NumAnalysis206.Conditioning.Errors.normwiseSize]
  · rw [rightHandSide_backwardError_eq]
    simp [Specs.NumAnalysis206.Conditioning.Errors.normwiseSize]

end NumAnalysis206.Conditioning
