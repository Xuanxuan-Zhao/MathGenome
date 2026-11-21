import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.NormToMeasure
import MathGenome.Internal.RealAnalysis.D11.Ch07.ConvergenceDefinitions
import MathGenome.Internal.RealAnalysis.D11.Ch05.MarkovZeroFinite
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Norm convergence implies global convergence in measure
(paper.tex:2126–2142), including its quantitative finite-exponent estimate. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
universe u
noncomputable section
namespace D11.Ch07.NormToMeasure

open D11.Ch07.ConvergenceDefinitions
open D11.Ch04.EssentialBounds
open D11.Ch04.AeCommonException

theorem deviation_bound : Specs.D11.Ch07.NormToMeasure.deviation_bound := by
  intro X 𝕜 _ _ _ _ μ f g p ε hf hg hp hε
  change μ (deviationSet f g ε) ≤
    ENNReal.ofReal (ε ^ (-p)) * powerIntegral μ p (fun x => f x - g x)
  have hp' : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpow : 0 < ε ^ p := Real.rpow_pos_of_pos hε p
  have hm : Measurable (fun x => ENNReal.ofReal (‖f x - g x‖ ^ p)) :=
    ((hf.sub hg).norm.pow_const p).ennreal_ofReal
  have hsub : deviationSet f g ε ⊆
      {x | ENNReal.ofReal (ε ^ p) ≤ ENNReal.ofReal (‖f x - g x‖ ^ p)} := by
    intro x hx
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow hε.le (le_of_lt hx) hp'.le)
  calc
    μ (deviationSet f g ε) ≤
        μ {x | ENNReal.ofReal (ε ^ p) ≤ ENNReal.ofReal (‖f x - g x‖ ^ p)} :=
      measure_mono hsub
    _ ≤ (∫⁻ x, ENNReal.ofReal (‖f x - g x‖ ^ p) ∂μ) /
        ENNReal.ofReal (ε ^ p) :=
      meas_ge_le_lintegral_div hm.aemeasurable
        (ne_of_gt (ENNReal.ofReal_pos.mpr hpow)) ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (ε ^ (-p)) * powerIntegral μ p (fun x => f x - g x) := by
      rw [powerIntegral_eq_lintegral, Real.rpow_neg hε.le,
        ENNReal.ofReal_inv_of_pos hpow, div_eq_mul_inv, mul_comm]

theorem lp_to_measure : Specs.D11.Ch07.NormToMeasure.lp_to_measure := by
  intro X 𝕜 _ _ _ _ μ f g p h
  change lpConverges μ p f g at h
  rcases h with ⟨hp, hg, hf, ht⟩
  change inMeasureConverges μ f g
  intro ε hε
  have hmul := ENNReal.Tendsto.const_mul ht
    (a := ENNReal.ofReal (ε ^ (-p))) (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at hmul
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul
    (fun _ => bot_le) (fun n => deviation_bound μ (f n) g p ε (hf n).1 hg.1 hp hε)

theorem linfty_to_measure : Specs.D11.Ch07.NormToMeasure.linfty_to_measure := by
  intro X 𝕜 _ _ _ _ μ f g h
  change linftyConverges μ f g at h
  change inMeasureConverges μ f g
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hev : ∀ᶠ n in atTop,
      essentialSupNorm μ (fun x => f n x - g x) < ENNReal.ofReal (ε / 2) :=
    h.2.2.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hhalf))
  apply tendsto_const_nhds.congr'
  filter_upwards [hev] with n hn
  have hb := (essentialSupNorm_le_iff μ (fun x => f n x - g x)
    ⟨ε / 2, hhalf.le⟩).mp (by
      convert hn.le using 1
      exact ENNReal.ofReal_coe_nnreal.symm)
  have hb := (almostEverywhere_iff_native μ _).mp hb
  symm
  apply measure_mono_null (t := {x | ¬ ‖f n x - g x‖ ≤ ε / 2})
  · intro x hx hle
    exact (not_lt_of_ge (hle.trans (half_le_self hε.le))) hx
  · exact ae_iff.mp hb

end D11.Ch07.NormToMeasure
