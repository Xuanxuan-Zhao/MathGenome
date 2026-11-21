import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.LocalBanachStep
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Conditioning.Neumann
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Newton.SegmentRemainder
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Newton.Definitions
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

noncomputable section

namespace NumAnalysis206.Newton

/-- Uniform inverse control and the quadratic Newton error on a root-centered ball. -/
theorem local_banach_step : Specs.NumAnalysis206.Newton.LocalBanachStepStatement := by
  intro 𝕜 _ X Y _ _ _ _ _ _ F U p A L R r hU hF hp hA hball hL hLip hr hrR
  dsimp only
  intro hsmall x hx
  let b := ‖A.symm.toContinuousLinearMap‖
  have hb : 0 ≤ b := norm_nonneg _
  have hxR : x ∈ Metric.closedBall p R := Metric.closedBall_subset_closedBall hrR hx
  have hpR : p ∈ Metric.closedBall p R := Metric.mem_closedBall_self (le_trans hr.le hrR)
  have hxr : ‖x - p‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  let D := fderiv 𝕜 F x - A.toContinuousLinearMap
  let E := A.symm.toContinuousLinearMap.comp D
  have hD : ‖D‖ ≤ L * ‖x - p‖ := by
    simpa only [D, hA] using hLip x hxR p hpR
  have hE : ‖E‖ ≤ b * L * r := by
    calc
      ‖E‖ ≤ b * ‖D‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ b * (L * ‖x - p‖) := mul_le_mul_of_nonneg_left hD hb
      _ ≤ b * (L * r) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hxr hL) hb
      _ = b * L * r := (mul_assoc _ _ _).symm
  obtain ⟨_, B, _, _, _, hB, hBinv, _⟩ :=
    NumAnalysis206.Conditioning.operatorInversePerturbation A D (lt_of_le_of_lt hE hsmall)
  have hBx : B.toContinuousLinearMap = fderiv 𝕜 F x := by
    simpa only [D, add_sub_cancel] using hB
  have hinv : (fderiv 𝕜 F x).inverse = B.symm.toContinuousLinearMap := by
    rw [← hBx, ContinuousLinearMap.inverse_equiv]
  have hden : 0 < 1 - b * L * r := sub_pos.mpr hsmall
  have hnorm : ‖(fderiv 𝕜 F x).inverse‖ ≤ b / (1 - b * L * r) := by
    rw [hinv]
    exact hBinv.trans (div_le_div_of_nonneg_left hb hden (by linarith))
  have hvalid : (fderiv 𝕜 F x).IsInvertible := ⟨B, hBx⟩
  have hid : operatorNewton (𝕜 := 𝕜) F x - p =
      (fderiv 𝕜 F x).inverse (F p - F x - fderiv 𝕜 F x (p - x)) := by
    simp only [operatorNewton, Specs.NumAnalysis206.Newton.operatorNewtonValue,
      hp, zero_sub, map_sub, map_neg, hvalid.inverse_apply_self]
    abel
  refine ⟨⟨hball hxR, (hF x (hball hxR)).differentiableAt (hU.mem_nhds (hball hxR)),
    hvalid⟩, hnorm, hid, ?_⟩
  let : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  have hrem := segment_remainder 𝕜 X Y F U (Metric.closedBall p R) L
    hU hF hball (convex_closedBall p R) hL hLip x hxR p hpR
  change ‖operatorNewton (𝕜 := 𝕜) F x - p‖ ≤ _
  rw [hid]
  calc
    ‖(fderiv 𝕜 F x).inverse (F p - F x - fderiv 𝕜 F x (p - x))‖ ≤
        ‖(fderiv 𝕜 F x).inverse‖ * ‖F p - F x - fderiv 𝕜 F x (p - x)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (b / (1 - b * L * r)) * ((L / 2) * ‖p - x‖ ^ 2) :=
      mul_le_mul hnorm hrem (norm_nonneg _) (by positivity)
    _ = (b * L / (2 * (1 - b * L * r))) * ‖x - p‖ ^ 2 := by
      rw [norm_sub_rev p x]
      field_simp

end NumAnalysis206.Newton
