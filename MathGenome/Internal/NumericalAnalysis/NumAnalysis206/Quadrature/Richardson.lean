import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.Richardson
import Mathlib.Analysis.Asymptotics.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section

open Filter Asymptotics Topology

namespace NumAnalysis206.Quadrature

/-- One-step Richardson extrapolation in exact arithmetic. -/
def richardson (p lam fine coarse : ℝ) : ℝ :=
  (lam ^ p * fine - coarse) / (lam ^ p - 1)

private theorem scale_tendsto {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun h : ℝ => h / lam) (𝓝[Set.Ioi 0] 0) (𝓝[Set.Ioi 0] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using (tendsto_id.div_const lam :
      Tendsto (fun h : ℝ => h / lam) (𝓝 (0 : ℝ)) (𝓝 (0 / lam))).mono_left
        nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
    exact div_pos hh hlam

private theorem scaled_power_bigO {lam s : ℝ} (hlam : 0 < lam) :
    (fun h : ℝ => (h / lam) ^ s) =O[𝓝[Set.Ioi 0] 0] (fun h => h ^ s) := by
  have hb := isBigO_const_mul_self (lam ^ s)⁻¹ (fun h : ℝ => h ^ s)
    (𝓝[Set.Ioi 0] 0)
  refine hb.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  rw [Real.div_rpow hh.le hlam.le]
  ring

/-- The leading real-power error cancels and the remainder has order `p + q`. -/
theorem extrapolation : Specs.NumAnalysis206.Quadrature.extrapolation := by
  intro approx A c p q lam hp _hq hlam hrem
  have hlampos : 0 < lam := lt_trans zero_lt_one hlam
  have hpow : 0 < lam ^ p := Real.rpow_pos_of_pos hlampos p
  have hden : lam ^ p - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (Real.one_lt_rpow hlam hp))
  have hscaled := (hrem.comp_tendsto (scale_tendsto hlampos)).trans
    (scaled_power_bigO (s := p + q) hlampos)
  have hb := ((hscaled.const_mul_left (lam ^ p)).sub hrem).const_mul_left
    (lam ^ p - 1)⁻¹
  refine hb.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  change (lam ^ p - 1)⁻¹ *
      (lam ^ p * (approx (h / lam) - (A + c * (h / lam) ^ p)) -
        (approx h - (A + c * h ^ p))) =
    Specs.NumAnalysis206.Quadrature.richardsonValue p lam (approx (h / lam)) (approx h) - A
  unfold Specs.NumAnalysis206.Quadrature.richardsonValue
  rw [Real.div_rpow hh.le hlampos.le]
  field_simp
  ring

/-- The exact linear combination propagates absolute errors by these weights. -/
theorem inputError : Specs.NumAnalysis206.Quadrature.inputError := by
  intro p lam fine coarse fineHat coarseHat δfine δcoarse hp hlam _hδfine _hδcoarse hf hc
  have hlampos : 0 < lam := lt_trans zero_lt_one hlam
  have hpow : 0 < lam ^ p := Real.rpow_pos_of_pos hlampos p
  have hden : 0 < lam ^ p - 1 := sub_pos.mpr (Real.one_lt_rpow hlam hp)
  unfold Specs.NumAnalysis206.Quadrature.richardsonValue
  rw [← sub_div, abs_div, abs_of_pos hden]
  apply div_le_div_of_nonneg_right _ hden.le
  calc
    |(lam ^ p * fineHat - coarseHat) - (lam ^ p * fine - coarse)| =
        |lam ^ p * (fineHat - fine) - (coarseHat - coarse)| := by
      congr 1
      ring
    _ ≤ |lam ^ p * (fineHat - fine)| + |coarseHat - coarse| := abs_sub _ _
    _ = lam ^ p * |fineHat - fine| + |coarseHat - coarse| := by
      rw [abs_mul, abs_of_pos hpow]
    _ ≤ lam ^ p * δfine + δcoarse := add_le_add (mul_le_mul_of_nonneg_left hf hpow.le) hc

end NumAnalysis206.Quadrature
