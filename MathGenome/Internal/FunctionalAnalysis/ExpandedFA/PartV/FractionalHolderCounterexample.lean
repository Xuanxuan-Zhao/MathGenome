import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.FractionalHolderCounterexample
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.FractionalIntegrals

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ExpandedFA.PartV.FractionalHolderCounterexample
open Spec
open ExpandedFA.PartV.FractionalHolder.Spec
open ExpandedFA.PartV.FractionalIntegrals

theorem input_conditions : InputConditions := by
  refine ⟨⟨1, by norm_num, ?_⟩, rfl, ?_⟩
  · intro x hx y hy
    have h₁ : |x-y| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hy.1, hx.2]⟩
    simpa [datum] using
      (Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg (x-y)) h₁
        (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (1/4:ℝ) ≤ 1))
  · exact ((continuous_fst.sub continuous_const).abs).rpow_const
      (fun _ => Or.inr (by norm_num))

/-- Evaluate the reflected integral by integrating t*r^(-3/4)-r^(1/4).
The endpoint r=0 is excluded by Ioc, so all power identities are valid. -/
lemma linear_power_integral {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in Ioc 0 t, (t-s) ^ (-3/4 : ℝ) * s) =
      (16/5 : ℝ) * t ^ (5/4 : ℝ) := by
  have h₁ : Integrable (fun r : ℝ => r ^ (-3/4 : ℝ)) (volume.restrict (Ioc 0 t)) := by
    simpa only [IntegrableOn, show (1/4 : ℝ)-1 = -3/4 by norm_num] using
      (power_integrable (α := (1/4 : ℝ)) (T := t) (by norm_num))
  have h₂ : Integrable (fun r : ℝ => r ^ (1/4 : ℝ)) (volume.restrict (Ioc 0 t)) := by
    simpa only [IntegrableOn, show (5/4 : ℝ)-1 = 1/4 by norm_num] using
      (power_integrable (α := (5/4 : ℝ)) (T := t) (by norm_num))
  have he : (fun r : ℝ => r ^ (-3/4 : ℝ) * (t-r)) =ᵐ[volume.restrict (Ioc 0 t)]
      (fun r => t * r ^ (-3/4 : ℝ) - r ^ (1/4 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hp : r ^ (-3/4 : ℝ) * r = r ^ (1/4 : ℝ) := by
      rw [← Real.rpow_add_one hr.1.ne']
      norm_num
    rw [mul_sub, hp]
    ring
  have href : (∫ s in Ioc 0 t, (t-s) ^ (-3/4 : ℝ) * s) =
      ∫ r in Ioc 0 t, r ^ (-3/4 : ℝ) * (t-r) := by
    rw [← intervalIntegral.integral_of_le ht, ← intervalIntegral.integral_of_le ht]
    simpa only [sub_sub_cancel, sub_self, sub_zero] using
      (intervalIntegral.integral_comp_sub_left
        (fun r : ℝ => r ^ (-3/4 : ℝ) * (t-r)) (a := (0 : ℝ)) (b := t) t)
  rw [href]
  rw [integral_congr_ae he,
    integral_sub (h₁.const_mul t) h₂,
    integral_const_mul]
  have hp₁ : (∫ r in Ioc 0 t, r ^ (-3/4 : ℝ)) = t ^ (1/4 : ℝ) / (1/4) := by
    simpa only [show (1/4 : ℝ)-1 = -3/4 by norm_num] using
      (power_integral (α := (1/4 : ℝ)) (T := t) (by norm_num) ht)
  have hp₂ : (∫ r in Ioc 0 t, r ^ (1/4 : ℝ)) = t ^ (5/4 : ℝ) / (5/4) := by
    simpa only [show (5/4 : ℝ)-1 = 1/4 by norm_num] using
      (power_integral (α := (5/4 : ℝ)) (T := t) (by norm_num) ht)
  rw [hp₁, hp₂]
  have hp : t * t ^ (1/4 : ℝ) = t ^ (5/4 : ℝ) := by
    calc
      _ = t ^ (1 : ℝ) * t ^ (1/4 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add' ht (by norm_num)]; norm_num
  nlinarith [hp]

lemma output_formula {t : ℝ} (ht : 0 ≤ t) :
    output t = (16/5 : ℝ) * t ^ (5/4 : ℝ) * |t-1/2| ^ (1/4 : ℝ) := by
  unfold output amplitudeValue amplitude datum
  simp only [smul_eq_mul]
  have he : (fun s : ℝ => (t-s) ^ ((1:ℝ)/4-1) * (|t-1/2| ^ (1/4 : ℝ) * s)) =
      (fun s => ((t-s) ^ (-3/4 : ℝ) * s) * |t-1/2| ^ (1/4 : ℝ)) := by
    funext s
    norm_num
    ring
  rw [he, integral_mul_const, linear_power_integral ht]

theorem integral_formula : IntegralFormula := by
  intro t ht
  refine ⟨?_, output_formula ht.1⟩
  have hi : IntegrableOn (fun s : ℝ => (t-s) ^ (-3/4 : ℝ) * s) (Ioc 0 t) := by
    have h := (reflected_power_integrable (α := (1/4 : ℝ)) (t := t) (by norm_num)).mul_continuousOn_of_subset
      continuousOn_id measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self
    simpa only [id_eq, show (1/4 : ℝ)-1 = -3/4 by norm_num] using h
  simpa only [IntegrableOn, amplitude, datum, mul_assoc, mul_left_comm, mul_comm] using
    hi.mul_const (|t-1/2| ^ (1/4 : ℝ))

lemma output_midpoint : output (1/2) = 0 := by
  rw [output_formula (by norm_num)]
  norm_num

theorem quotient_formula : QuotientFormula := by
  intro h ht hh
  unfold quotient
  rw [output_formula ht, output_midpoint, sub_zero,
    Real.norm_of_nonneg (by positivity)]
  have hbase : 1/2+h-1/2 = h := by ring
  rw [hbase]
  have hp : |h| ^ (1/4 : ℝ) / |h| ^ (1/2 : ℝ) = |h| ^ (-1/4 : ℝ) := by
    rw [← Real.rpow_sub (abs_pos.mpr hh)]
    norm_num
  rw [mul_div_assoc, hp]

theorem quotient_divergence : QuotientDivergence := by
  have hc : Tendsto (fun h : ℝ => (16/5 : ℝ) * (1/2+h) ^ (5/4 : ℝ))
      (𝓝[≠] 0) (𝓝 ((16/5 : ℝ) * (1/2 : ℝ) ^ (5/4 : ℝ))) := by
    have hcont : Continuous (fun h : ℝ => (16/5 : ℝ) * (1/2+h) ^ (5/4 : ℝ)) := by
      fun_prop
    simpa using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hp := (tendsto_rpow_neg_nhdsGT_zero (by norm_num : (-1/4 : ℝ) < 0)).comp
    tendsto_abs_nhdsNE_zero
  have hm := hc.pos_mul_atTop (by positivity) hp
  apply hm.congr'
  have hn : ∀ᶠ h : ℝ in 𝓝[≠] 0, 0 ≤ 1/2+h := by
    have hn : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ), -(1/2 : ℝ) < h :=
      eventually_gt_nhds (by norm_num)
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with h hh
    linarith
  filter_upwards [hn, self_mem_nhdsWithin] with h hh hne
  exact (quotient_formula h hh hne).symm

theorem local_failure : LocalFailure := by
  rintro ⟨C, δ, hδ, hb⟩
  have hlarge : ∀ᶠ h in 𝓝[≠] (0 : ℝ), C < quotient h :=
    quotient_divergence.eventually (eventually_gt_atTop C)
  have habs : Tendsto (fun h : ℝ => |h|) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ h : ℝ in 𝓝[≠] 0, |h| < min δ (1/2 : ℝ) :=
    habs.eventually (eventually_lt_nhds (lt_min hδ (by norm_num)))
  obtain ⟨h, hl, hs, hn⟩ := (hlarge.and (hsmall.and self_mem_nhdsWithin)).exists
  have hδh := lt_of_lt_of_le hs (min_le_left _ _)
  have hhalf := lt_of_lt_of_le hs (min_le_right _ _)
  have ht : 1/2+h ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨h₁, h₂⟩ := abs_lt.mp hhalf
    constructor <;> linarith
  have hbound := hb (1/2+h) ht (by simpa using hδh)
  have hpos : 0 < |h| ^ (1/2 : ℝ) := Real.rpow_pos_of_pos (abs_pos.mpr hn) _
  have hle : quotient h ≤ C := by
    rw [quotient, div_le_iff₀ hpos]
    simpa using hbound
  exact (not_lt_of_ge hle) hl

theorem global_failure : GlobalFailure := by
  rintro ⟨C, hC, hb⟩
  apply local_failure
  refine ⟨C, 1, by norm_num, ?_⟩
  intro t ht _
  exact hb t ht (1/2) (by constructor <;> norm_num)

end ExpandedFA.PartV.FractionalHolderCounterexample
