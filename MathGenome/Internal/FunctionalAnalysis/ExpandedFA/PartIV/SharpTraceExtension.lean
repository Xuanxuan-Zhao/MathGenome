import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SharpTraceExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.SharpTraceBound
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.SobolevCompleteness
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators

namespace ExpandedFA.PartIV.SharpTraceExtension
open ExpandedFA.Distributions ExpandedFA.PartIV.FractionalSobolev

lemma translation_representative {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : Domain n)
    (u : Lp 𝕜 p (volume : Measure (Domain n))) :
    translation p a u =ᵐ[volume] fun x => u (x - a) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_sub_right volume a)

@[simp] lemma translation_zero {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : Lp 𝕜 p (volume : Measure (Domain n))) :
    translation p (0 : Domain n) u = u := by
  apply Lp.ext
  filter_upwards [translation_representative p (0 : Domain n) u] with x hx
  simpa using hx

lemma translation_continuous {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : Lp 𝕜 p (volume : Measure (Domain n))) :
    Continuous (fun a => translation p a u) :=
  lpTranslation_continuous p hp u

lemma lpIncrement_translation {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a h : Domain n)
    (u : Lp 𝕜 p (volume : Measure (Domain n))) :
    lpIncrement p h (translation p a u) = translation p a (lpIncrement p h u) := by
  apply Lp.ext
  have hc := (measurePreserving_sub_right (volume : Measure (Domain n)) a).quasiMeasurePreserving.ae_eq_comp (lpIncrement_representative p u h)
  have ht := (measurePreserving_add_right (volume : Measure (Domain n)) h).quasiMeasurePreserving.ae_eq_comp (translation_representative p a u)
  filter_upwards [lpIncrement_representative p (translation p a u) h,
    translation_representative p a (lpIncrement p h u), hc, ht,
    translation_representative p a u] with x hx hy hz ht hu
  dsimp only [Function.comp_apply] at hz ht
  rw [hx, hy, hz, ht, hu]
  congr 1
  congr 1
  abel

lemma differenceEnergy_translation {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (a : Domain n)
    (u : Lp 𝕜 p (volume : Measure (Domain n))) :
    differenceEnergy s p (translation p a u) = differenceEnergy s p u := by
  simp only [difference_energy_weighted_integral s p hp, lpIncrement_translation,
    (translation p a).enorm_map]

lemma increment_translation_error_bound {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a h : Domain n)
    (u : Lp 𝕜 p (volume : Measure (Domain n))) :
    ‖lpIncrement p h (translation p a u - u)‖ₑ ≤ 2 * ‖lpIncrement p h u‖ₑ := by
  rw [map_sub, lpIncrement_translation]
  exact enorm_sub_le.trans (by simp [two_mul, (translation p a).enorm_map])

/-- The weighted increment energy of a translation error tends to zero.
Dominated convergence is on the h-variable; the dominating function is
2^p times the integrable increment energy of u. No smoothness is assumed. -/
lemma translation_error_energy_tendsto {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : FractionalSpace 𝕜 n s p) :
    Tendsto (fun a => differenceEnergy s p (translation p a u.val - u.val))
      (𝓝 (0 : Domain n)) (𝓝 0) := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp
  let F := fun a h : Domain n =>
    ‖lpIncrement p h (translation p a u.val - u.val)‖ₑ ^ p.toReal
  let B := fun h : Domain n => (2 * ‖lpIncrement p h u.val‖ₑ) ^ p.toReal
  have hmeas : ∀ a, Measurable (F a) := fun a =>
    (lpIncrement_continuous p hp (translation p a u.val - u.val)).enorm.measurable.pow_const _
  have hbound : ∀ a h, F a h ≤ B h := fun a h =>
    ENNReal.rpow_le_rpow (increment_translation_error_bound p a h u.val) hp0.le
  have hfin : ∫⁻ h, B h ∂differenceMeasure s p ≠ ∞ := by
    simp only [B, ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    rw [lintegral_const_mul _ ((lpIncrement_continuous p hp u.val).enorm.measurable.pow_const _),
      ← difference_energy_weighted_integral s p hp]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0.le (by norm_num)) u.property.ne
  have hlim : ∀ h, Tendsto (fun a => F a h) (𝓝 (0 : Domain n)) (𝓝 0) := by
    intro h
    have hc : Continuous (fun a => lpIncrement p h (translation p a u.val - u.val)) :=
      (SharpTraceBound.lpIncrement_continuous_input p h).comp
        ((translation_continuous p hp u.val).sub continuous_const)
    have hh := ((ENNReal.continuous_rpow_const (y := p.toReal)).comp hc.enorm).tendsto
      (0 : Domain n)
    convert hh using 1 <;> simp only [F, Function.comp_apply, translation_zero, sub_self, map_zero,
      enorm_zero, ENNReal.zero_rpow_of_pos hp0] <;> rfl
  have hd := tendsto_lintegral_filter_of_dominated_convergence B
    (Eventually.of_forall hmeas)
    (Eventually.of_forall fun a => ae_of_all _ (hbound a)) hfin
    (ae_of_all _ hlim)
  simpa only [F, lintegral_zero, ← difference_energy_weighted_integral s p hp] using hd

/-- Translation is strongly continuous for the full fractional norm. -/
theorem fractional_translation_continuous :
    Specs.ExpandedFA.PartIV.SharpTraceExtension.FractionalTranslationContinuous := by
  intro 𝕜 _ n s p _ hp u
  have h₁ := ((translation_continuous p hp u.val).sub (continuous_const (y := u.val))).norm.tendsto
    (0 : Domain n)
  simp only [Pi.sub_apply, translation_zero, sub_self, norm_zero] at h₁
  have h₂ := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (translation_error_energy_tendsto s p hp u)
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp
  have h₃ := (Real.continuous_rpow_const (one_div_pos.mpr hp0).le).tendsto (0 : ℝ)
  have hsum := h₁.add (h₃.comp h₂)
  simpa only [fractionalError, Function.comp_apply, ENNReal.toReal_zero,
    Real.zero_rpow (one_div_pos.mpr hp0).ne', zero_add] using hsum

lemma lintegral_sublevel_swap {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (r : X → ℝ) (hr : Measurable r) (hr0 : ∀ x, 0 ≤ r x)
    (F : X → ℝ≥0∞)
    (hF : Measurable F) (W : ℝ → ℝ≥0∞) (hW : Measurable W) :
    (∫⁻ t in Ioi (0 : ℝ), W t * ∫⁻ h in {h : X | r h < t}, F h ∂ν) =
      ∫⁻ h, F h * (∫⁻ t in Ioi (r h), W t) ∂ν := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hnear (t : ℝ) : (∫⁻ h in {h : X | r h < t}, F h ∂ν) =
      ∫⁻ h, {h : X | r h < t}.indicator F h ∂ν := by
    rw [lintegral_indicator (measurableSet_lt hr measurable_const)]
  have hfar (h : X) :
      (∫⁻ t, (Ioi (r h)).indicator W t ∂μ) =
        ∫⁻ t in Ioi (r h), W t := by
    rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_left.mpr (Ioi_subset_Ioi (hr0 h))]
  have hm : Measurable (fun z : ℝ × X =>
      W z.1 * {h : X | r h < z.1}.indicator F z.2) := by
    have he : (fun z : ℝ × X =>
        {h : X | r h < z.1}.indicator F z.2) =
        {z : ℝ × X | r z.2 < z.1}.indicator (fun z => F z.2) := by
      funext z
      simp only [indicator_apply, mem_ofPred_eq]
    apply Measurable.mul (hW.comp measurable_fst)
    rw [he]
    exact (hF.comp measurable_snd).indicator
      (measurableSet_lt (hr.comp measurable_snd) measurable_fst)
  calc
    _ = ∫⁻ t, ∫⁻ h, W t * {h : X | r h < t}.indicator F h ∂ν ∂μ := by
      apply lintegral_congr
      intro t
      rw [hnear, lintegral_const_mul _ (hF.indicator
        (measurableSet_lt hr measurable_const))]
    _ = ∫⁻ h, ∫⁻ t, W t * {h : X | r h < t}.indicator F h ∂μ ∂ν :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ h, F h * ∫⁻ t, (Ioi (r h)).indicator W t ∂μ ∂ν := by
      apply lintegral_congr
      intro h
      rw [← lintegral_const_mul _ (hW.indicator measurableSet_Ioi)]
      apply lintegral_congr
      intro t
      by_cases ht : r h < t <;> simp [ht, mul_comm]
    _ = _ := by simp_rw [hfar]


lemma scale_lintegral_swap {n : ℕ} (F : Domain n → ℝ≥0∞)
    (hF : Measurable F) (W : ℝ → ℝ≥0∞) (hW : Measurable W) :
    (∫⁻ t in Ioi (0 : ℝ), W t * ∫⁻ h in {h : Domain n | euclideanLength h < t}, F h) =
      ∫⁻ h, F h * ∫⁻ t in Ioi (euclideanLength h), W t :=
  lintegral_sublevel_swap volume euclideanLength euclideanLength_continuous.measurable
    (fun _ => norm_nonneg _) F hF W hW

lemma translation_increment_neg {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (h : Domain n)
    (u : Lp 𝕜 p (volume : Measure (Domain n))) :
    translation p h (lpIncrement p h u) = - lpIncrement p (-h) u := by
  apply Lp.ext
  have hc := (measurePreserving_sub_right (volume : Measure (Domain n)) h).quasiMeasurePreserving.ae_eq_comp (lpIncrement_representative p u h)
  filter_upwards [translation_representative p h (lpIncrement p h u), hc,
    Lp.coeFn_neg (lpIncrement p (-h) u), lpIncrement_representative p u (-h)] with x ht hc hn hi
  change lpIncrement p h u (x-h) = u ((x-h)+h) - u (x-h) at hc
  rw [ht, hc, hn]
  simp only [Pi.neg_apply]
  rw [hi]
  simp only [sub_add_cancel, sub_eq_add_neg, add_neg_cancel_right]
  abel

lemma lpIncrement_enorm_neg {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (h : Domain n)
    (u : Lp 𝕜 p (volume : Measure (Domain n))) :
    ‖lpIncrement p (-h) u‖ₑ = ‖lpIncrement p h u‖ₑ := by
  rw [← enorm_neg, ← translation_increment_neg]
  exact (translation p h).enorm_map _

/-- Integrating the scale-t derivative majorant gives exactly the sharp
fractional kernel, rather than a weaker exponent. The nonzero-increment
hypothesis is necessary because the adopted kernel is zero at the origin. -/
lemma derivative_scale_kernel {n : ℕ} (p : ℝ≥0∞) (hp1 : 1 < p) (hp : p ≠ ∞)
    (h : Domain n) (hh : h ≠ 0) :
    ∫⁻ t in Ioi (euclideanLength h), ENNReal.ofReal t ^ (-((n : ℝ) + p.toReal)) =
      ENNReal.ofReal (1 / ((n : ℝ) + p.toReal - 1)) *
        differenceKernel (1 - 1 / p.toReal) p h := by
  have hpr : 1 < p.toReal := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).mpr hp1
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr : 0 < euclideanLength h := by
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm ((euclideanLength_eq_zero h).not.mpr hh))
  rw [SharpTraceBound.AnalyticEstimates.power_lintegral_far (by linarith) hr, differenceKernel, if_neg hh]
  have hexp : -((n : ℝ) + p.toReal) + 1 =
      -((n : ℝ) + (1 - 1 / p.toReal) * p.toReal) := by
    rw [SharpTraceBound.endpoint_weight hp1 hp]
    ring
  have hc : -(1 / (-((n : ℝ) + p.toReal) + 1)) =
      1 / ((n : ℝ) + p.toReal - 1) := by
    rw [show -((n : ℝ) + p.toReal) + 1 = -((n : ℝ) + p.toReal - 1) by ring]
    simp only [one_div, inv_neg, neg_neg]
  rw [hc, hexp]

lemma derivative_scale_kernel_radius {n : ℕ} (p : ℝ≥0∞) (hp1 : 1 < p) (hp : p ≠ ∞)
    (R : ℝ) (hR : 0 < R) (h : Domain n) (hh : h ≠ 0) :
    ∫⁻ t in Ioi (euclideanLength h / R), ENNReal.ofReal t ^ (-((n : ℝ) + p.toReal)) =
      (ENNReal.ofReal R ^ ((n : ℝ) + p.toReal - 1) *
        ENNReal.ofReal (1 / ((n : ℝ) + p.toReal - 1))) *
        differenceKernel (1 - 1 / p.toReal) p h := by
  have hpr : 1 < p.toReal := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).mpr hp1
  have hr : 0 < euclideanLength h := by
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm ((euclideanLength_eq_zero h).not.mpr hh))
  rw [SharpTraceBound.AnalyticEstimates.power_lintegral_far (by linarith [Nat.cast_nonneg (α := ℝ) n])
    (div_pos hr hR)]
  have hc : -(1 / (-((n : ℝ) + p.toReal) + 1)) =
      1 / ((n : ℝ) + p.toReal - 1) := by
    rw [show -((n : ℝ) + p.toReal) + 1 = -((n : ℝ) + p.toReal - 1) by ring]
    simp only [one_div, inv_neg, neg_neg]
  have he : -((n : ℝ) + p.toReal) + 1 = -((n : ℝ) + p.toReal - 1) := by ring
  have hek : -(↑n + (1 - 1 / p.toReal) * p.toReal) = -((n : ℝ) + p.toReal - 1) := by
    rw [SharpTraceBound.endpoint_weight hp1 hp]
    ring
  have hpow : ENNReal.ofReal (euclideanLength h / R) ^ (-((n : ℝ) + p.toReal - 1)) =
      ENNReal.ofReal R ^ ((n : ℝ) + p.toReal - 1) *
        ENNReal.ofReal (euclideanLength h) ^ (-((n : ℝ) + p.toReal - 1)) := by
    rw [ENNReal.ofReal_div_of_pos hR, div_eq_mul_inv,
      ENNReal.mul_rpow_of_ne_zero (ENNReal.ofReal_pos.mpr hr).ne'
        (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top),
      ENNReal.inv_rpow]
    simp only [ENNReal.rpow_neg, inv_inv]
    ac_rfl
  rw [hc, he, hpow, differenceKernel, if_neg hh, hek]
  ac_rfl

/-- Tonelli turns the derivative scale majorant into the sharp fractional energy.
The zero-increment condition covers dimension zero without discarding a point
of positive measure. -/
lemma derivative_scale_integral {n : ℕ} (p : ℝ≥0∞) (hp1 : 1 < p) (hp : p ≠ ∞)
    (F : Domain n → ℝ≥0∞) (hF : Measurable F) (hF0 : F 0 = 0) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal t ^ (-((n : ℝ) + p.toReal)) *
      ∫⁻ h in {h : Domain n | euclideanLength h < t}, F h) =
      ENNReal.ofReal (1 / ((n : ℝ) + p.toReal - 1)) *
        ∫⁻ h, differenceKernel (1 - 1 / p.toReal) p h * F h := by
  rw [scale_lintegral_swap F hF (fun t : ℝ => ENNReal.ofReal t ^ (-((n : ℝ) + p.toReal)))
    (measurable_id.ennreal_ofReal.pow_const _)]
  calc
    _ = ∫⁻ h, ENNReal.ofReal (1 / ((n : ℝ) + p.toReal - 1)) *
        (differenceKernel (1 - 1 / p.toReal) p h * F h) := by
      apply lintegral_congr
      intro h
      by_cases hh : h = 0
      · simp [hh, hF0]
      · rw [derivative_scale_kernel p hp1 hp h hh]
        ac_rfl
    _ = _ := lintegral_const_mul _ ((differenceKernel_measurable _ p).mul hF)

lemma derivative_increment_integral {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞)
    (u : Lp 𝕜 p (volume : Measure (Domain n))) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal t ^ (-((n : ℝ) + p.toReal)) *
      ∫⁻ h in {h : Domain n | euclideanLength h < t}, ‖lpIncrement p h u‖ₑ ^ p.toReal) =
      ENNReal.ofReal (1 / ((n : ℝ) + p.toReal - 1)) *
        differenceEnergy (1 - 1 / p.toReal) p u := by
  have hpr : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  have hi0 : lpIncrement p (0 : Domain n) u = 0 := by
    apply Lp.ext
    filter_upwards [lpIncrement_representative p u (0 : Domain n),
      Lp.coeFn_zero 𝕜 p (volume : Measure (Domain n))] with x hx hz
    simp only [add_zero, sub_self] at hx
    exact hx.trans hz.symm
  rw [derivative_scale_integral p hp1 hp _
    ((lpIncrement_continuous p hp u).enorm.measurable.pow_const _) (by
      simp only [hi0, enorm_zero, ENNReal.zero_rpow_of_pos hpr])]
  congr 1
  rw [difference_energy_weighted_integral _ p hp]
  exact (lintegral_withDensity_eq_lintegral_mul _ (differenceKernel_measurable _ p)
      ((lpIncrement_continuous p hp u).enorm.measurable.pow_const _)).symm


/-- Dominated convergence for the powers defining a finite Lp norm. The
bound belongs to Lp; no finite-measure assumption is needed. -/
lemma eLpNorm_tendsto_zero_of_dominated {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (f : ℕ → X → F) (g : X → ℝ)
    (hf : ∀ k, AEStronglyMeasurable (f k) μ) (hg : MemLp g p μ)
    (hbound : ∀ k, ∀ᵐ x ∂μ, ‖f k x‖ ≤ ‖g x‖)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => f k x) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (f k) p μ) atTop (𝓝 0) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hfin : (∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ) ≠ ∞ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hg.eLpNorm_lt_top).ne
  have hd := tendsto_lintegral_of_dominated_convergence'
    (fun x => ‖g x‖ₑ ^ p.toReal)
    (fun k => (hf k).enorm.pow_const p.toReal)
    (fun k => (hbound k).mono fun x hx =>
      ENNReal.rpow_le_rpow (by simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal hx) hpr.le)
    hfin (hlim.mono fun x hx => by
      simpa only [Function.comp_def, enorm_zero, ENNReal.zero_rpow_of_pos hpr] using
        ((ENNReal.continuous_rpow_const (y := p.toReal)).tendsto 0).comp (by simpa only [enorm_zero] using hx.enorm))
  simp only [lintegral_zero] at hd
  have ht := ((ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0).comp hd
  simpa only [Function.comp_def, Function.comp_apply, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (hf _),
    ENNReal.zero_rpow_of_pos (one_div_pos.mpr hpr)] using ht

/-- If Lp convergence to zero has an Lp majorant for all increments, it is
convergence in the full fractional norm. -/
lemma fractionalError_tendsto_zero_of_increment_bound {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (v : ℕ → Lp 𝕜 p (volume : Measure (Domain n)))
    (hv : Tendsto v atTop (𝓝 0)) (B : Domain n → ℝ)
    (hB : MemLp B p (differenceMeasure s p))
    (hbound : ∀ k h, ‖lpIncrement p h (v k)‖ ≤ ‖B h‖) :
    Tendsto (fun k => fractionalError s p (v k) 0) atTop (𝓝 0) := by
  have hi := eLpNorm_tendsto_zero_of_dominated (differenceMeasure s p) p hp
    (fun k h => lpIncrement p h (v k)) B
    (fun k => (lpIncrement_continuous p hp (v k)).stronglyMeasurable.aestronglyMeasurable)
    hB (fun k => ae_of_all _ (hbound k)) (ae_of_all _ fun h => by
      simpa only [Function.comp_def, Function.comp_apply, map_zero] using
        (SharpTraceBound.lpIncrement_continuous_input p h).continuousAt.tendsto.comp hv)
  have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hi
  have hn := hv.norm
  simp only [norm_zero] at hn
  have hsum := hn.add ht
  simpa only [Function.comp_def, Function.comp_apply, fractionalError, sub_zero, ENNReal.toReal_rpow,
    difference_energy_weightedLp 𝕜 n s p hp, ENNReal.toReal_zero, zero_add] using hsum

/-- Uniformly bounded Lipschitz multipliers converging pointwise to one
approximate every finite-energy datum in the full fractional norm. This is
the truncation step of density, including dimension zero and p=1. -/
lemma fractional_multipliers_tendsto {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hs0 : 0 < s) (hs1 : s < 1)
    (hp : p ≠ ∞) (a : ℕ → Domain n → 𝕜) (M L : ℝ≥0)
    (hM : ∀ k x, ‖a k x‖ ≤ M)
    (hL : ∀ k x y, ‖a k x - a k y‖ ≤ L * euclideanLength (x - y))
    (ha : ∀ x, Tendsto (fun k => a k x) atTop (𝓝 1))
    (u : FractionalSpace 𝕜 n s p) :
    Tendsto (fun k => fractionalError s p
      (fractionalMultiply s p hs0 hs1 hp (a k) M L (hM k) (hL k) u).val u.val)
      atTop (𝓝 0) := by
  let v := fun k => (fractionalMultiply s p hs0 hs1 hp (a k) M L (hM k) (hL k) u).val - u.val
  let b := fun k x => a k x - 1
  have hbM : ∀ k x, ‖b k x‖ ≤ (M + 1 : ℝ≥0) := by
    intro k x
    exact (norm_sub_le _ _).trans (by simpa using add_le_add_right (hM k x) 1)
  have hbL : ∀ k x y, ‖b k x - b k y‖ ≤ L * euclideanLength (x - y) := by
    intro k x y
    simpa only [b, sub_sub_sub_cancel_right] using hL k x y
  have hvrep : ∀ k, v k =ᵐ[volume] fun x => b k x * u.val x := by
    intro k
    filter_upwards [Lp.coeFn_sub _ u.val,
      fractionalMultiply_representative s p hs0 hs1 hp (a k) M L (hM k) (hL k) u] with x hx hy
    change v k x = _
    rw [hx, Pi.sub_apply, hy]
    dsimp only [b]
    ring
  have hraw := eLpNorm_tendsto_zero_of_dominated (volume : Measure (Domain n)) p hp
    (fun k x => b k x * u.val x) (fun x => ((M : ℝ) + 1) * ‖u.val x‖)
    (fun k => (((euclideanLipschitz_continuous (a k) L (hL k)).sub continuous_const).stronglyMeasurable.mul
      (Lp.stronglyMeasurable u.val)).aestronglyMeasurable)
    ((Lp.memLp u.val).norm.const_mul ((M : ℝ) + 1))
    (fun k => ae_of_all _ fun x => by
      rw [norm_mul, Real.norm_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_right (hbM k x) (norm_nonneg _))
    (ae_of_all _ fun x => by
      simpa only [sub_self, zero_mul] using (ha x).sub_const 1 |>.mul_const (u.val x))
  have hnv : Tendsto (fun k => ‖v k‖) atTop (𝓝 0) := by
    have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hraw
    have heq : (fun k => ‖v k‖) = (fun k => (eLpNorm (fun x => b k x * u.val x) p volume).toReal) := by
      funext k
      rw [← toReal_enorm, Lp.enorm_def, eLpNorm_congr_ae (hvrep k)]
    rw [heq]
    simpa only [Function.comp_def, Function.comp_apply, ENNReal.toReal_zero] using ht
  have hv : Tendsto v atTop (𝓝 0) := (tendsto_zero_iff_norm_tendsto_zero).mpr hnv
  let K : ℝ := max (L : ℝ) (2 * (M + 1 : ℝ≥0))
  let B := fun h : Domain n => ((M : ℝ) + 1) * ‖lpIncrement p h u.val‖ +
    (K * ‖u.val‖) * incrementCutoff h
  have hBi : MemLp B p (differenceMeasure s p) :=
    (((finite_energy_iff_memLp s p hp u.val).mp u.property).norm.const_mul ((M : ℝ) + 1)).add
      ((incrementCutoff_memLp s p hs0 hs1 hp).const_mul (K * ‖u.val‖))
  have hbound : ∀ k h, ‖lpIncrement p h (v k)‖ ≤ ‖B h‖ := by
    intro k h
    rw [Real.norm_of_nonneg]
    · have hb := bounded_mul_increment_norm p (b k) (M + 1) L (hbM k) (hbL k)
        u.val (v k) (hvrep k) h
      convert hb using 1 <;> dsimp [B, K] <;> push_cast <;> ring
    · dsimp only [B]
      exact add_nonneg (mul_nonneg (by positivity) (norm_nonneg _))
        (mul_nonneg (mul_nonneg (le_trans L.coe_nonneg (le_max_left _ _)) (norm_nonneg _))
          (incrementCutoff_nonneg h))
  simpa only [fractionalError, sub_zero, v] using
    fractionalError_tendsto_zero_of_increment_bound s p hp v hv B hBi hbound

/-- Dilations of one smooth bump give compact cutoffs with a uniform
Lipschitz constant and pointwise limit one. -/
lemma exists_smooth_cutoffs (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    ∃ (L : ℝ≥0) (a : ℕ → Domain n → 𝕜),
      (∀ k, ContDiff ℝ (↑(⊤ : ℕ∞)) (a k) ∧ HasCompactSupport (a k)) ∧
      (∀ k x, ‖a k x‖ ≤ 1) ∧
      (∀ k x y, ‖a k x - a k y‖ ≤ L * euclideanLength (x - y)) ∧
      (∀ x, Tendsto (fun k => a k x) atTop (𝓝 1)) := by
  let b : ContDiffBump (0 : Domain n) := ⟨1, 2, by norm_num, by norm_num⟩
  have hbc : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => b x) := b.contDiff
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    b.hasCompactSupport hbc (by simp)
  let q := fun k : ℕ => 1 / ((k : ℝ) + 1)
  have hqpos : ∀ k, 0 < q k := fun k => by dsimp [q]; positivity
  have hqle : ∀ k, q k ≤ 1 := fun k => by
    dsimp [q]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
  let a := fun (k : ℕ) (x : Domain n) => (b (q k • x) : 𝕜)
  refine ⟨L, a, ?_, ?_, ?_, ?_⟩
  · intro k
    refine ⟨?_, ?_⟩
    · simpa only [a, Function.comp_def, RCLike.ofRealCLM_apply, id_eq] using
        (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp (hbc.comp (contDiff_id.const_smul (q k)))
    · exact (b.hasCompactSupport.comp_smul (hqpos k).ne').comp_left (RCLike.ofReal_zero)
  · intro k x
    simpa only [a, RCLike.norm_ofReal, abs_of_nonneg b.nonneg] using
      (b.le_one (x := q k • x))
  · intro k x y
    have hb := hL.dist_le_mul (q k • x) (q k • y)
    simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hqpos k)] at hb
    have hn : q k * ‖x - y‖ ≤ euclideanLength (x - y) :=
      (mul_le_of_le_one_left (norm_nonneg _) (hqle k)).trans (norm_le_euclideanLength _)
    have h := hb.trans (mul_le_mul_of_nonneg_left hn L.coe_nonneg)
    simpa only [a, ← RCLike.ofReal_sub, RCLike.norm_ofReal, Real.norm_eq_abs] using h
  · intro x
    have hq : Tendsto q atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hx := b.continuous.continuousAt.tendsto.comp (hq.smul_const x)
    have hb0 : b (0 : Domain n) = 1 := b.one_of_mem_closedBall (by simp [b])
    have hreal : Tendsto (fun k => b (q k • x)) atTop (𝓝 1) := by
      simpa only [Function.comp_def, zero_smul, hb0] using hx
    simpa only [a, Function.comp_def, RCLike.ofRealCLM_apply, RCLike.ofReal_one] using
      (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).continuous.continuousAt.tendsto.comp hreal

/-- Compactly supported representatives are dense for the full fractional
norm. The representatives need not yet be smooth; convolution is the
remaining regularization step. -/
theorem compact_fractional_approximation {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hs0 : 0 < s) (hs1 : s < 1)
    (hp : p ≠ ∞) (u : FractionalSpace 𝕜 n s p) (ε : ℝ) (hε : 0 < ε) :
    ∃ (v : FractionalSpace 𝕜 n s p) (f : Domain n → 𝕜),
      StronglyMeasurable f ∧ HasCompactSupport f ∧ v.val =ᵐ[volume] f ∧
        fractionalError s p v.val u.val < ε := by
  obtain ⟨L, a, hac, haM, haL, ha⟩ := exists_smooth_cutoffs 𝕜 n
  have ht := fractional_multipliers_tendsto s p hs0 hs1 hp a 1 L haM haL ha u
  obtain ⟨k, hk⟩ := (ht.eventually (Iio_mem_nhds hε)).exists
  refine ⟨fractionalMultiply s p hs0 hs1 hp (a k) 1 L (haM k) (haL k) u,
    fun x => a k x * u.val x,
    (hac k).1.continuous.stronglyMeasurable.mul (Lp.stronglyMeasurable u.val),
    (hac k).2.mul_right, ?_, hk⟩
  exact fractionalMultiply_representative s p hs0 hs1 hp (a k) 1 L (haM k) (haL k) u

/-- The weighted increment measure is sigma finite even when its mass near
the origin is infinite. Its density is finite at every point. -/
instance differenceMeasure_sigmaFinite {n : ℕ} (s : ℝ) (p : ℝ≥0∞) :
    SigmaFinite (differenceMeasure (d := n) s p) := by
  apply SigmaFinite.withDensity_of_ne_top'
  intro h
  by_cases hh : h = 0
  · simp [hh]
  · rw [differenceKernel, if_neg hh]
    apply ENNReal.rpow_ne_top_of_ne_zero _ ENNReal.ofReal_ne_top
    exact (ENNReal.ofReal_pos.mpr (lt_of_le_of_ne (norm_nonneg _)
      (Ne.symm ((euclideanLength_eq_zero h).not.mpr hh)))).ne'

/-- The scalar product-space realization of the difference seminorm. -/
def rawSeminorm {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (s : ℝ) (p : ℝ≥0∞)
    (f : Domain n → 𝕜) : ℝ≥0∞ :=
  eLpNorm (fun z : Domain n × Domain n => f (z.2 + z.1) - f z.2) p
    ((differenceMeasure s p).prod volume)

lemma rawSeminorm_eq {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    {n : ℕ} (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : Lp 𝕜 p (volume : Measure (Domain n))) (f : Domain n → 𝕜)
    (hf : Measurable f) (huf : u =ᵐ[volume] f) :
    rawSeminorm s p f = differenceEnergy s p u ^ (1 / p.toReal) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hm : Measurable (fun z : Domain n × Domain n => f (z.2 + z.1) - f z.2) :=
    (hf.comp (measurable_snd.add measurable_fst)).sub (hf.comp measurable_snd)
  have he : (∫⁻ z : Domain n × Domain n, ‖f (z.2 + z.1) - f z.2‖ₑ ^ p.toReal
      ∂((differenceMeasure s p).prod volume)) = differenceEnergy s p u := by
    rw [lintegral_prod _ (hm.enorm.pow_const _).aemeasurable,
      difference_energy_representative 𝕜 n s p u f huf]
    exact lintegral_withDensity_eq_lintegral_mul _ (differenceKernel_measurable s p)
      (hm.enorm.pow_const _).lintegral_prod_right'
  rw [rawSeminorm, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hm.aestronglyMeasurable, he]

/-- Minkowski in the scalar product-space realization controls the entire
fractional convolution error by the translation errors of the input. -/
lemma rawSeminorm_convolution_error_le {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] {n : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (φ : Domain n → ℝ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hφn : ∀ y, 0 ≤ φ y) (hφmass : ∫ y, φ y = 1)
    (f : Domain n → 𝕜) (hf : Measurable f) (hfi : LocallyIntegrable f volume)
    (η : ℝ≥0∞) (hη : η ≠ ∞)
    (hcontrol : ∀ y ∈ Function.support φ,
      rawSeminorm s p (fun x => f (x - y) - f x) ≤ η) :
    rawSeminorm s p (convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) volume - f) ≤ η := by
  let μ : Measure (Domain n × Domain n) := (differenceMeasure s p).prod volume
  let F : (Domain n × Domain n) × Domain n → 𝕜 := fun z =>
    φ z.2 • ((f (z.1.2 + z.1.1 - z.2) - f (z.1.2 + z.1.1)) -
      (f (z.1.2 - z.2) - f z.1.2))
  have hF : Measurable F := by
    exact (hφc.measurable.comp measurable_snd).smul
      (((hf.comp ((measurable_snd.comp measurable_fst).add
        (measurable_fst.comp measurable_fst) |>.sub measurable_snd)).sub
        (hf.comp ((measurable_snd.comp measurable_fst).add (measurable_fst.comp measurable_fst)))).sub
        ((hf.comp ((measurable_snd.comp measurable_fst).sub measurable_snd)).sub
          (hf.comp (measurable_snd.comp measurable_fst))))
  have hs (y : Domain n) : eLpNorm (fun z => F (z,y)) p μ ≤ ‖φ y‖ₑ * η := by
    change eLpNorm ((φ y) • (fun z : Domain n × Domain n =>
      (f (z.2 + z.1 - y) - f (z.2 + z.1)) - (f (z.2 - y) - f z.2))) p μ ≤ _
    rw [eLpNorm_const_smul]
    by_cases hy : y ∈ Function.support φ
    · gcongr
      exact hcontrol y hy
    · simp [Function.notMem_support.mp hy]
  have hφi : Integrable φ volume := hφc.integrable_of_hasCompactSupport hφs
  have hmass : (∫⁻ y, ‖φ y‖ₑ) = 1 := by
    simp_rw [← ofReal_norm, Real.norm_of_nonneg (hφn _)]
    rw [← ofReal_integral_eq_lintegral_ofReal hφi (ae_of_all _ hφn), hφmass, ENNReal.ofReal_one]
  have hb : (∫⁻ y, eLpNorm (fun z => F (z,y)) p μ) ≤ η := by
    calc
      _ ≤ ∫⁻ y, ‖φ y‖ₑ * η := lintegral_mono hs
      _ = η := by rw [lintegral_mul_const _ hφc.measurable.enorm, hmass, one_mul]
  have hm := (minkowski_integral_eLpNorm μ volume p Fact.out hp F hF
    (hb.trans_lt (lt_top_iff_ne_top.mpr hη))).2
  let E := fun x y : Domain n => φ y • (f (x - y) - f x)
  have hc : ∀ x, Integrable (fun y => φ y • f (x - y)) volume :=
    hφs.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hφc hfi
  have hE : ∀ x, Integrable (E x) volume := by
    intro x
    have hsub := (hc x).sub (hφi.smul_const (f x))
    change Integrable (fun y => φ y • f (x - y) - φ y • f x) volume at hsub
    simpa only [E, smul_sub] using hsub
  have hEi : ∀ x, (∫ y, E x y) = convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) volume x - f x := by
    intro x
    simp only [E, smul_sub]
    rw [integral_sub (hc x) (hφi.smul_const (f x)), integral_smul_const, hφmass, one_smul]
    rfl
  have heq : (fun z : Domain n × Domain n => ∫ y, F (z,y)) =
      (fun z => (convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) volume - f) (z.2 + z.1) -
        (convolution φ f (ContinuousLinearMap.lsmul ℝ ℝ) volume - f) z.2) := by
    funext z
    have hz : (fun y => F (z,y)) = (fun y => E (z.2 + z.1) y - E z.2 y) := by
      funext y
      dsimp only [F, E]
      rw [smul_sub]
    rw [hz, integral_sub (hE (z.2 + z.1)) (hE z.2), hEi, hEi]
    rfl
  rw [heq] at hm
  exact hm.trans hb

open ExpandedFA.Distributions.SmoothApproximateIdentitiesSpec

lemma rawSeminorm_translation_error_tendsto {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] {n : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : FractionalSpace 𝕜 n s p) (f : Domain n → 𝕜)
    (hf : Measurable f) (huf : u.val =ᵐ[volume] f) :
    Tendsto (fun y => rawSeminorm s p (fun x => f (x - y) - f x)) (𝓝 0) (𝓝 0) := by
  have heq (y : Domain n) : rawSeminorm s p (fun x => f (x - y) - f x) =
      differenceEnergy s p (translation p y u.val - u.val) ^ (1 / p.toReal) := by
    apply rawSeminorm_eq s p hp _ _ ((hf.comp (measurable_id.sub_const y)).sub hf)
    have hc := (measurePreserving_sub_right (volume : Measure (Domain n)) y).quasiMeasurePreserving.ae_eq_comp huf
    filter_upwards [Lp.coeFn_sub (translation p y u.val) u.val,
      translation_representative p y u.val, hc, huf] with x hx ht hc hu
    simp only [Pi.sub_apply] at hx
    dsimp only [Function.comp_apply] at hc
    rw [hx, ht, hc, hu]
    rfl
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp
  have ht := ((ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0).comp
    (translation_error_energy_tendsto s p hp u)
  simpa only [Function.comp_def, ← heq, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp0)] using ht

/-- Mollification converges in the difference seminorm, not only in Lp. -/
lemma mollify_rawSeminorm_tendsto {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] {n : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (ρ : Domain n → ℝ) (hρ : IsMollifier ρ)
    (u : FractionalSpace 𝕜 n s p) (f : Domain n → 𝕜)
    (hf : Measurable f) (huf : u.val =ᵐ[volume] f) :
    Tendsto (fun ε => rawSeminorm s p (MollifyValue ρ ε f - f))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hflp : MemLp f p volume := (Lp.memLp u.val).ae_eq huf
  apply ENNReal.tendsto_nhds_zero.mpr
  intro η hη
  by_cases hηt : η = ∞
  · simp [hηt]
  have ht := ENNReal.tendsto_nhds_zero.mp
    (rawSeminorm_translation_error_tendsto s p hp u f hf huf) η hη
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp ht
  filter_upwards [scaledKernel_support_eventually ρ hρ.2.1 hr,
    self_mem_nhdsWithin] with ε hs hε
  have hk := scaledKernel_properties ρ hρ ε hε
  exact rawSeminorm_convolution_error_le s p hp (ScaledKernelValue ρ ε)
    hk.1.continuous hk.2.1 hk.2.2.1 hk.2.2.2 f hf (hflp.locallyIntegrable Fact.out)
    η hηt (fun y hy => hball (hs hy))

/-- Compactly supported fractional data can be mollified in the full
fractional norm. The weighted product-space bound also proves finite energy
of the approximation selected here. -/
lemma smooth_approximation_of_compact_support {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] {n : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : FractionalSpace 𝕜 n s p) (f : Domain n → 𝕜)
    (hf : StronglyMeasurable f) (hfc : HasCompactSupport f)
    (huf : u.val =ᵐ[volume] f) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (v : FractionalSpace 𝕜 n s p) (g : Domain n → 𝕜),
      ContDiff ℝ (↑(⊤ : ℕ∞)) g ∧ HasCompactSupport g ∧ v.val =ᵐ[volume] g ∧
        fractionalError s p v.val u.val < δ := by
  obtain ⟨ρ, hρ⟩ := ExpandedFA.Sobolev.Smoothing.exists_mollifier n
  have hflp : MemLp f p volume := (Lp.memLp u.val).ae_eq huf
  have htlp := (mollify_lp ρ hρ p Fact.out hp f hflp).2
  have htraw := mollify_rawSeminorm_tendsto s p hp ρ hρ u f hf.measurable huf
  have ht := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htlp).add
    ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htraw)
  simp only [ENNReal.toReal_zero, zero_add] at ht
  have hev := ht.eventually (Iio_mem_nhds hδ)
  have hsmall := htraw.eventually (Iio_mem_nhds (show (0 : ℝ≥0∞) < 1 by simp))
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, htpos, hterr, htr⟩ := (hpos.and (hev.and hsmall)).exists
  let g := MollifyValue ρ t f
  have hk := scaledKernel_properties ρ hρ t htpos
  have hgc : ContDiff ℝ (↑(⊤ : ℕ∞)) g :=
    hk.2.1.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      hk.1 (hflp.locallyIntegrable Fact.out)
  have hgcs : HasCompactSupport g :=
    HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hk.2.1 hfc
  have hglp : MemLp g p volume := mollify_memLp ρ hρ p Fact.out f hflp htpos
  let w := (hglp.sub hflp).toLp (g - f)
  have hwr : w =ᵐ[volume] g - f := (hglp.sub hflp).coeFn_toLp
  have hraw := rawSeminorm_eq s p hp w (g - f)
    (hgc.continuous.measurable.sub hf.measurable) hwr
  have hpr : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp
  have hwfin : differenceEnergy s p w < ∞ := by
    apply (ENNReal.rpow_lt_top_iff_of_pos (one_div_pos.mpr hpr)).mp
    rw [← hraw]
    exact htr.trans (by simp)
  let v : FractionalSpace 𝕜 n s p :=
    ⟨w + u.val, finite_energy_add s p hp w u.val hwfin u.property⟩
  refine ⟨v, g, hgc, hgcs, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_add w u.val, hwr, huf] with x hx hw hu
    change (w + u.val) x = g x
    rw [hx]
    change w x + u.val x = g x
    rw [hw, hu]
    simp
  · have hnorm : ‖w‖ = (eLpNorm (g - f) p volume).toReal := by
      rw [← toReal_enorm, Lp.enorm_def, eLpNorm_congr_ae hwr]
    change ‖w + u.val - u.val‖ +
      (differenceEnergy s p (w + u.val - u.val)).toReal ^ (1 / p.toReal) < δ
    rw [add_sub_cancel_right, hnorm, ENNReal.toReal_rpow, ← hraw]
    exact hterr

/-- Smooth compactly supported functions are dense in the full fractional
norm, for every dimension and both manuscript scalar fields. -/
theorem smooth_density : Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothDensity := by
  intro 𝕜 _ n s hs0 hs1 p _ hp u ε hε
  letI : Fact (p ≠ ∞) := ⟨hp⟩
  letI : MeasurableSpace 𝕜 := borel 𝕜
  obtain ⟨v, f, hf, hfc, hvf, hvu⟩ :=
    compact_fractional_approximation s p hs0 hs1 hp u (ε / 2) (half_pos hε)
  obtain ⟨w, g, hg, hgc, hwg, hwv⟩ :=
    smooth_approximation_of_compact_support s p hp v f hf hfc hvf (ε / 2) (half_pos hε)
  refine ⟨w, g, hg, hgc, hwg, ?_⟩
  have htri : fractionalError s p w.val u.val ≤
      fractionalError s p w.val v.val + fractionalError s p v.val u.val := by
    change ‖w - u‖ ≤ ‖w - v‖ + ‖v - u‖
    calc
      ‖w - u‖ = ‖(w - v) + (v - u)‖ := by congr 1; abel
      _ ≤ ‖w - v‖ + ‖v - u‖ := norm_add_le _ _
  linarith

namespace KernelEstimates
lemma integral_enorm_rpow_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α}
    (p : ℝ) (hp : 1 ≤ p) (f : α → E) (hf : AEStronglyMeasurable f μ) :
    ‖∫ x, f x ∂μ‖ₑ ^ p ≤ (μ univ) ^ (p - 1) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have h := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ (f := f)
    (μ := μ) zero_lt_one hp hf
  rw [eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm] at h
  simp only [div_one, ENNReal.rpow_one] at h
  calc
    _ ≤ (∫⁻ x, ‖f x‖ₑ ∂μ) ^ p :=
      ENNReal.rpow_le_rpow (enorm_integral_le_lintegral_enorm f) hp0.le
    _ ≤ ((∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1 / p) * (μ univ) ^ (1 - 1 / p)) ^ p :=
      ENNReal.rpow_le_rpow h hp0.le
    _ = (μ univ) ^ (p - 1) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul,
        ← ENNReal.rpow_mul]
      have h₁ : 1 / p * p = 1 := by field_simp
      have h₂ : (1 - 1 / p) * p = p - 1 := by field_simp
      rw [h₁, h₂, ENNReal.rpow_one, mul_comm]
lemma bounded_kernel_integral_rpow_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α}
    (p : ℝ) (hp : 1 ≤ p) (S : Set α) (K : α → ℝ) (F : α → E)
    (hK : AEStronglyMeasurable K (μ.restrict S))
    (hF : AEStronglyMeasurable F (μ.restrict S)) (A : ℝ≥0∞)
    (hA : ∀ᵐ y ∂μ.restrict S, ‖K y‖ₑ ≤ A) :
    ‖∫ y in S, K y • F y ∂μ‖ₑ ^ p ≤
      (μ S) ^ (p - 1) * A ^ p * ∫⁻ y in S, ‖F y‖ₑ ^ p ∂μ := by
  have hp0 : 0 ≤ p := (show 0 ≤ (1 : ℝ) by norm_num).trans hp
  have h := integral_enorm_rpow_le p hp (fun y => K y • F y) (hK.smul hF)
  simp only [Measure.restrict_apply_univ] at h
  apply h.trans
  calc
    (μ S) ^ (p - 1) * ∫⁻ y in S, ‖K y • F y‖ₑ ^ p ∂μ ≤
        (μ S) ^ (p - 1) * ∫⁻ y in S, A ^ p * ‖F y‖ₑ ^ p ∂μ := by
      gcongr 1
      apply lintegral_mono_ae
      filter_upwards [hA] with y hy
      rw [enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ hp0]
      gcongr
    _ = _ := by
      rw [lintegral_const_mul'' _ (hF.enorm.pow_const p), mul_assoc]

lemma supported_kernel_integral_rpow_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α}
    (p : ℝ) (hp : 1 ≤ p) (S : Set α) (K : α → ℝ) (F : α → E)
    (hK : AEStronglyMeasurable K (μ.restrict S))
    (hF : AEStronglyMeasurable F (μ.restrict S))
    (hS : ∀ y, y ∉ S → K y = 0) (A : ℝ≥0∞)
    (hA : ∀ᵐ y ∂μ.restrict S, ‖K y‖ₑ ≤ A) :
    ‖∫ y, K y • F y ∂μ‖ₑ ^ p ≤
      (μ S) ^ (p - 1) * A ^ p * ∫⁻ y in S, ‖F y‖ₑ ^ p ∂μ := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun y hy => by rw [hS y hy, zero_smul])]
  exact bounded_kernel_integral_rpow_le p hp S K F hK hF A hA
lemma integral_kernel_eq_integral_sub_of_integral_zero {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} (K : α → ℝ) (F : α → E) (c : E)
    (hK : Integrable K μ) (hKF : Integrable (fun y => K y • F y) μ)
    (hz : ∫ y, K y ∂μ = 0) :
    (∫ y, K y • F y ∂μ) = ∫ y, K y • (F y - c) ∂μ := by
  simp_rw [smul_sub]
  rw [integral_sub hKF (hK.smul_const c), integral_smul_const, hz, zero_smul, sub_zero]

lemma supported_kernel_lintegral_rpow_le {X Y E : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    (p : ℝ) (hp : 1 ≤ p) (S : Set Y) (K : Y → ℝ) (F : X × Y → E)
    (hK : Measurable K) (hF : Measurable F)
    (hS : ∀ y, y ∉ S → K y = 0) (A : ℝ≥0∞)
    (hA : ∀ᵐ y ∂ν.restrict S, ‖K y‖ₑ ≤ A) :
    (∫⁻ x, ‖∫ y, K y • F (x, y) ∂ν‖ₑ ^ p ∂μ) ≤
      (ν S) ^ (p - 1) * A ^ p * ∫⁻ y in S, ∫⁻ x, ‖F (x, y)‖ₑ ^ p ∂μ ∂ν := by
  have hpow : Measurable (fun z : X × Y => ‖F z‖ₑ ^ p) := hF.enorm.pow_const p
  calc
    _ ≤ ∫⁻ x, (ν S) ^ (p - 1) * A ^ p *
        ∫⁻ y in S, ‖F (x, y)‖ₑ ^ p ∂ν ∂μ := by
      apply lintegral_mono
      intro x
      exact supported_kernel_integral_rpow_le p hp S K (fun y => F (x, y))
        hK.aestronglyMeasurable.restrict
        (hF.comp measurable_prodMk_left).aestronglyMeasurable.restrict hS A hA
    _ = _ := by
      rw [lintegral_const_mul _ hpow.lintegral_prod_right',
        lintegral_lintegral_swap hpow.aemeasurable]
open ExpandedFA.Distributions ExpandedFA.PartIV.FractionalSobolev
lemma integral_representative_sub_increment {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : Lp 𝕜 p (volume : Measure (Domain n))) (f : Domain n → 𝕜)
    (huf : u =ᵐ[volume] f) (h : Domain n) :
    (∫⁻ x, ‖f (x - h) - f x‖ₑ ^ p.toReal) =
      ‖lpIncrement p (-h) u‖ₑ ^ p.toReal := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hpR : p.toReal ≠ 0 := (ENNReal.toReal_pos hp0 hp).ne'
  have heq : lpIncrement p (-h) u =ᵐ[volume] fun x => f (x-h) - f x := by
    have hs := (measurePreserving_sub_right volume h).quasiMeasurePreserving.ae_eq_comp huf
    filter_upwards [lpIncrement_representative p u (-h), huf, hs] with x hx hux hsh
    simpa only [sub_eq_add_neg, Function.comp_apply] using hx.trans (congrArg₂ (· - ·) hsh hux)
  rw [← lintegral_congr_ae (heq.mono (fun x hx => congrArg (fun z : 𝕜 => ‖z‖ₑ ^ p.toReal) hx))]
  rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (Lp.aestronglyMeasurable _),
    ← ENNReal.rpow_mul, one_div_mul_cancel hpR, ENNReal.rpow_one]

lemma mean_zero_kernel_increment_bound {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : Lp 𝕜 p (volume : Measure (Domain n))) (f : Domain n → 𝕜)
    (hf : Continuous f) (huf : u =ᵐ[volume] f)
    (S : Set (Domain n)) (K : Domain n → ℝ)
    (hK : Continuous K) (hKc : HasCompactSupport K)
    (hS : ∀ y, y ∉ S → K y = 0) (hzero : ∫ y, K y = 0)
    (A : ℝ≥0∞) (hA : ∀ᵐ y ∂volume.restrict S, ‖K y‖ₑ ≤ A) :
    (∫⁻ x, ‖∫ y, K y • f (x - y)‖ₑ ^ p.toReal) ≤
      (volume S) ^ (p.toReal - 1) * A ^ p.toReal *
        ∫⁻ h in S, ‖lpIncrement p (-h) u‖ₑ ^ p.toReal := by
  let : MeasurableSpace 𝕜 := borel 𝕜
  have hpR : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  have hconv (x : Domain n) : Integrable (fun y => K y • f (x-y)) :=
    (hK.smul (hf.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hKc.smul_right
  have hcancel (x : Domain n) : (∫ y, K y • f (x-y)) = ∫ y, K y • (f (x-y)-f x) :=
    integral_kernel_eq_integral_sub_of_integral_zero K _ (f x)
      (hK.integrable_of_hasCompactSupport hKc) (hconv x) hzero
  simp_rw [hcancel]
  have hb := supported_kernel_lintegral_rpow_le (μ := volume) (ν := volume)
    p.toReal hpR S K (fun z : Domain n × Domain n => f (z.1-z.2)-f z.1)
    hK.measurable (((hf.comp (continuous_fst.sub continuous_snd)).sub
      (hf.comp continuous_fst)).measurable) hS A hA
  simpa only [integral_representative_sub_increment p hp u f huf] using hb
end KernelEstimates

lemma kernel_directional_compact {n : ℕ} (ρ : Domain n → ℝ)
    (hρs : HasCompactSupport ρ) (v : Domain n) :
    HasCompactSupport (fun x => fderiv ℝ ρ x v) :=
  (hρs.fderiv ℝ).comp_left (g := fun L : Domain n →L[ℝ] ℝ => L v) (by simp)

lemma kernel_directional_integrable {n : ℕ} (ρ : Domain n → ℝ)
    (hρs : HasCompactSupport ρ) (hρc : ContDiff ℝ 1 ρ) (v : Domain n) :
    Integrable (fun x => fderiv ℝ ρ x v) volume :=
  ((hρc.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
    (kernel_directional_compact ρ hρs v)

lemma kernel_directional_integral_zero {n : ℕ} (ρ : Domain n → ℝ)
    (hρs : HasCompactSupport ρ) (hρc : ContDiff ℝ 1 ρ) (v : Domain n) :
    ∫ x, fderiv ℝ ρ x v = 0 := by
  have hi := kernel_directional_integrable ρ hρs hρc v
  have hρi : Integrable ρ volume := hρc.continuous.integrable_of_hasCompactSupport hρs
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (Domain n))) (f := fun _ => (1 : ℝ)) (g := ρ) (v := v)
    (by simp) (by simpa using hi) (by simpa using hρi)
    (fun _ _ => differentiableAt_const _) (fun x _ => (hρc.differentiable one_ne_zero).differentiableAt)
  simpa using h

lemma kernel_directional_bound {n : ℕ} (ρ : Domain n → ℝ)
    (hρs : HasCompactSupport ρ) (hρc : ContDiff ℝ 1 ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x v, ‖fderiv ℝ ρ x v‖ ≤ C * ‖v‖ := by
  obtain ⟨C, hC⟩ := (hρs.fderiv ℝ).exists_bound_of_continuous
    (hρc.continuous_fderiv one_ne_zero)
  refine ⟨max C 0, le_max_right _ _, fun x v => ?_⟩
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right ((hC x).trans (le_max_left _ _)) (norm_nonneg _))


open ExpandedFA.Distributions.SmoothApproximateIdentitiesSpec

lemma scaledKernel_directional_formula {n : ℕ} (ρ : Domain n → ℝ)
    (hρc : Differentiable ℝ ρ) (t : ℝ) (x v : Domain n) :
    fderiv ℝ (ScaledKernelValue ρ t) x v =
      (t ^ n)⁻¹ * t⁻¹ * fderiv ℝ ρ (t⁻¹ • x) v := by
  have hc := (hρc (t⁻¹ • x)).hasFDerivAt.comp x
    ((ContinuousLinearMap.id ℝ (Domain n)).hasFDerivAt.const_smul t⁻¹)
  have hm := hc.const_mul ((t ^ n)⁻¹)
  change HasFDerivAt (ScaledKernelValue ρ t) _ x at hm
  rw [hm.fderiv]
  simp [mul_assoc]

lemma scaledKernel_directional_integral_zero {n : ℕ} (ρ : Domain n → ℝ)
    (hρs : HasCompactSupport ρ) (hρc : ContDiff ℝ 1 ρ)
    (t : ℝ) (v : Domain n) :
    ∫ x, (t ^ n)⁻¹ * t⁻¹ * fderiv ℝ ρ (t⁻¹ • x) v = 0 := by
  by_cases ht : t = 0
  · simp [ht]
  have hcs : HasCompactSupport (ScaledKernelValue ρ t) := by
    exact (hρs.comp_isClosedEmbedding (Homeomorph.smul (Units.mk0 t⁻¹ (inv_ne_zero ht))).isClosedEmbedding).mul_left
  have hcc : ContDiff ℝ 1 (ScaledKernelValue ρ t) :=
    contDiff_const.mul (hρc.comp (contDiff_id.const_smul t⁻¹))
  simpa only [scaledKernel_directional_formula ρ (hρc.differentiable one_ne_zero)] using
    kernel_directional_integral_zero (ScaledKernelValue ρ t) hcs hcc v


lemma convolution_directional_formula {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (hρs : HasCompactSupport ρ) (hρc : ContDiff ℝ 1 ρ)
    (f : Domain n → 𝕜) (hf : LocallyIntegrable f volume) (x v : Domain n) :
    fderiv ℝ (convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume) x v =
      ∫ y, fderiv ℝ ρ y v • f (x - y) := by
  let L : ℝ →L[ℝ] 𝕜 →L[ℝ] 𝕜 := ContinuousLinearMap.lsmul ℝ ℝ
  have hd := hρs.hasFDerivAt_convolution_left L hρc hf x
  have hi := (hρs.fderiv ℝ).convolutionExists_left (L.precompL (Domain n))
    (hρc.continuous_fderiv one_ne_zero) hf x
  rw [hd.fderiv]
  change (∫ y, L.precompL (Domain n) (fderiv ℝ ρ y) (f (x - y))) v = _
  rw [ContinuousLinearMap.integral_apply hi]
  rfl

lemma scaledKernel_convolution_directional_formula {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (hρs : HasCompactSupport ρ) (hρc : ContDiff ℝ 1 ρ)
    (f : Domain n → 𝕜) (hf : LocallyIntegrable f volume)
    (t : ℝ) (ht : t ≠ 0) (x v : Domain n) :
    fderiv ℝ (MollifyValue ρ t f) x v =
      ∫ y, ((t ^ n)⁻¹ * t⁻¹ * fderiv ℝ ρ (t⁻¹ • y) v) • f (x - y) := by
  have hcs : HasCompactSupport (ScaledKernelValue ρ t) :=
    (hρs.comp_isClosedEmbedding (Homeomorph.smul (Units.mk0 t⁻¹ (inv_ne_zero ht))).isClosedEmbedding).mul_left
  have hcc : ContDiff ℝ 1 (ScaledKernelValue ρ t) :=
    contDiff_const.mul (hρc.comp (contDiff_id.const_smul t⁻¹))
  simpa only [MollifyValue, scaledKernel_directional_formula ρ (hρc.differentiable one_ne_zero)] using
    convolution_directional_formula (ScaledKernelValue ρ t) hcs hcc f hf x v


lemma mollify_eq_signed_average {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜) (t : ℝ) (ht : 0 < t) (x : Domain n) :
    MollifyValue ρ t f x = ∫ y, ρ y • f (x - t • y) := by
  have hscale := Measure.integral_comp_inv_smul_of_nonneg volume
    (fun y => ρ y • f (x - t • y)) ht.le
  simp only [smul_inv_smul₀ ht.ne', Module.finrank_pi, Fintype.card_fin] at hscale
  change (∫ y, ((t ^ n)⁻¹ * ρ (t⁻¹ • y)) • f (x - y)) = _
  simp_rw [mul_smul]
  rw [integral_smul, hscale, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ ht.ne'), one_smul]


namespace KernelEstimates
open ExpandedFA.Distributions ExpandedFA.PartIV.FractionalSobolev

def normalKernel {n : ℕ} (ρ : Domain n → ℝ) (z : Domain n) : ℝ :=
  -(n : ℝ) * ρ z - fderiv ℝ ρ z z

lemma coordinate_moment_derivative_integral {n : ℕ} (ρ : Domain n → ℝ)
    (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ) (j : Fin n) :
    (∫ z, z j * fderiv ℝ ρ z (Pi.single j 1)) = -(∫ z, ρ z) := by
  have hd : Continuous (fun z => fderiv ℝ ρ z (Pi.single j 1)) :=
    (hρ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hproj : fderiv ℝ (fun z : Domain n => z j) = fun _ => ContinuousLinearMap.proj j := by
    funext z
    exact (ContinuousLinearMap.proj j : Domain n →L[ℝ] ℝ).fderiv
  have hi₁ : Integrable (fun z : Domain n =>
      fderiv ℝ (fun z : Domain n => z j) z (Pi.single j 1) * ρ z) := by
    simpa [hproj] using hρ.continuous.integrable_of_hasCompactSupport hρc
  have hi₂ : Integrable (fun z : Domain n => z j * fderiv ℝ ρ z (Pi.single j 1)) :=
    ((continuous_apply j).mul hd).integrable_of_hasCompactSupport (hρc.fderiv_apply ℝ (Pi.single j 1)).mul_left
  have hi₃ : Integrable (fun z : Domain n => z j * ρ z) :=
    ((continuous_apply j).mul hρ.continuous).integrable_of_hasCompactSupport hρc.mul_left
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun z : Domain n => z j) (g := ρ) (v := Pi.single j 1) hi₁ hi₂ hi₃
    (fun z _ => (ContinuousLinearMap.proj j : Domain n →L[ℝ] ℝ).differentiableAt)
    (fun z _ => hρ.differentiable_one z)
  simpa [hproj] using h
lemma normalKernel_continuous {n : ℕ} (ρ : Domain n → ℝ)
    (hρ : ContDiff ℝ 1 ρ) : Continuous (normalKernel ρ) := by
  exact (continuous_const.mul hρ.continuous).sub
    ((hρ.continuous_fderiv one_ne_zero).clm_apply continuous_id)

lemma normalKernel_hasCompactSupport {n : ℕ} (ρ : Domain n → ℝ)
    (hρc : HasCompactSupport ρ) : HasCompactSupport (normalKernel ρ) := by
  have hd : HasCompactSupport (fun z => fderiv ℝ ρ z z) := by
    apply (hρc.fderiv ℝ).mono
    intro z hz hzero
    exact hz (by dsimp only; rw [hzero, zero_apply])
  exact (hρc.mul_left).sub hd

lemma normalKernel_integral {n : ℕ} (ρ : Domain n → ℝ)
    (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ) :
    (∫ z, normalKernel ρ z) = 0 := by
  have hdiag (z : Domain n) : fderiv ℝ ρ z z =
      ∑ j : Fin n, z j * fderiv ℝ ρ z (Pi.single j 1) := by
    calc
      _ = fderiv ℝ ρ z (∑ j, z j • Pi.single j 1) := congrArg _ (pi_eq_sum_univ' z)
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
  have hi (j : Fin n) : Integrable (fun z : Domain n => z j * fderiv ℝ ρ z (Pi.single j 1)) := by
    apply ((continuous_apply j).mul
      ((hρ.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
    exact (hρc.fderiv_apply ℝ (Pi.single j 1)).mul_left
  have hdi : Integrable (fun z => fderiv ℝ ρ z z) := by
    simp_rw [hdiag]
    exact integrable_finsetSum _ (fun j _ => hi j)
  simp only [normalKernel]
  rw [integral_sub ((hρ.continuous.integrable_of_hasCompactSupport hρc).const_mul _) hdi,
    integral_const_mul]
  simp_rw [hdiag]
  rw [integral_finsetSum _ (fun j _ => hi j)]
  simp_rw [coordinate_moment_derivative_integral ρ hρ hρc]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring
lemma hasDerivAt_scaledKernel {n : ℕ} (ρ : Domain n → ℝ)
    (hρ : ContDiff ℝ 1 ρ) (h : Domain n) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun r : ℝ => (r ^ n)⁻¹ * ρ (r⁻¹ • h))
      ((t ^ (n + 1))⁻¹ * normalKernel ρ (t⁻¹ • h)) t := by
  have hinv : HasDerivAt (fun r : ℝ => r⁻¹ • h) (-(t ^ 2)⁻¹ • h) t :=
    (hasDerivAt_inv ht).smul_const h
  have hrho := ((hρ.differentiable_one (t⁻¹ • h)).hasFDerivAt).comp_hasDerivAt t hinv
  have hz := hasDerivAt_zpow (-(n : ℤ)) t (Or.inl ht)
  have hp := hz.mul hrho
  convert hp using 1
  · funext r
    simp [zpow_neg, Function.comp_def]
  · simp only [Int.cast_neg, Int.cast_natCast, zpow_neg, zpow_natCast,
      normalKernel, map_smul, smul_eq_mul] at *
    rw [show -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) by omega,
      zpow_neg, zpow_natCast] at hp ⊢
    dsimp only [Function.comp_def]
    field_simp
    <;> ring
def derivativeScaledKernel {n : ℕ} (K : Domain n → ℝ) (t : ℝ) (h : Domain n) : ℝ :=
  (t ^ (n + 1))⁻¹ * K (t⁻¹ • h)

lemma derivativeScaledKernel_integral_zero {n : ℕ} (K : Domain n → ℝ)
    (hK : ∫ z, K z = 0) {t : ℝ} (ht : 0 < t) :
    (∫ h, derivativeScaledKernel K t h) = 0 := by
  simp only [derivativeScaledKernel, integral_const_mul]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume K ht.le, hK, smul_zero, mul_zero]

lemma derivativeScaledKernel_continuous {n : ℕ} (K : Domain n → ℝ)
    (hK : Continuous K) (t : ℝ) : Continuous (derivativeScaledKernel K t) := by
  unfold derivativeScaledKernel
  fun_prop

lemma derivativeScaledKernel_hasCompactSupport {n : ℕ} (K : Domain n → ℝ)
    (hK : HasCompactSupport K) {t : ℝ} (ht : t ≠ 0) :
    HasCompactSupport (derivativeScaledKernel K t) :=
  (hK.comp_isClosedEmbedding
    (Homeomorph.smul (Units.mk0 t⁻¹ (inv_ne_zero ht))).isClosedEmbedding).mul_left

lemma euclideanLength_smul {n : ℕ} (t : ℝ) (h : Domain n) :
    euclideanLength (t • h) = |t| * euclideanLength h := by
  change ‖t • WithLp.toLp 2 h‖ = |t| * ‖WithLp.toLp 2 h‖
  rw [norm_smul, Real.norm_eq_abs]

lemma derivativeScaledKernel_bounds {n : ℕ} (K : Domain n → ℝ)
    (hK : Continuous K) (hKc : HasCompactSupport K) :
    ∃ R M : ℝ, 0 < R ∧ 0 < M ∧ ∀ t : ℝ, 0 < t →
      (∀ h, ‖derivativeScaledKernel K t h‖ ≤ M * (t ^ (n + 1))⁻¹) ∧
      (∀ h, R * t < euclideanLength h → derivativeScaledKernel K t h = 0) := by
  obtain ⟨R, hR⟩ := hKc.bddAbove_image euclideanLength_continuous.continuousOn
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuous hK
  refine ⟨max R 1, max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro t ht
  have hpow : 0 ≤ (t ^ (n + 1))⁻¹ := inv_nonneg.mpr (pow_nonneg ht.le _)
  constructor
  · intro h
    simp only [derivativeScaledKernel, norm_mul, Real.norm_of_nonneg hpow]
    calc
      _ ≤ (t ^ (n + 1))⁻¹ * max M 1 := by gcongr; exact (hM _).trans (le_max_left _ _)
      _ = _ := mul_comm _ _
  · intro h hh
    have hvanish : K (t⁻¹ • h) = 0 := by
      by_contra hne
      have hb : euclideanLength (t⁻¹ • h) ≤ max R 1 :=
        (hR (mem_image_of_mem _ (subset_tsupport _ hne))).trans (le_max_left _ _)
      rw [euclideanLength_smul, abs_of_pos (inv_pos.mpr ht)] at hb
      have hh' : euclideanLength h ≤ max R 1 * t := by
        calc
          _ = t * (t⁻¹ * euclideanLength h) := by field_simp
          _ ≤ t * max R 1 := mul_le_mul_of_nonneg_left hb ht.le
          _ = _ := mul_comm _ _
      exact (not_le_of_gt hh) hh'
    simp only [derivativeScaledKernel, hvanish, mul_zero]
end KernelEstimates

lemma derivative_scale_integral_radius {n : ℕ} (p : ℝ≥0∞) (hp1 : 1 < p) (hp : p ≠ ∞)
    (R : ℝ) (hR : 0 < R) (F : Domain n → ℝ≥0∞) (hF : Measurable F) (hF0 : F 0 = 0) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal t ^ (-((n : ℝ) + p.toReal)) *
      ∫⁻ h in {h : Domain n | euclideanLength h < R * t}, F h) =
      (ENNReal.ofReal R ^ ((n : ℝ) + p.toReal - 1) *
        ENNReal.ofReal (1 / ((n : ℝ) + p.toReal - 1))) *
        ∫⁻ h, differenceKernel (1 - 1 / p.toReal) p h * F h := by
  have hset (t : ℝ) : {h : Domain n | euclideanLength h < R * t} =
      {h : Domain n | euclideanLength h / R < t} := by
    ext h
    simp only [mem_ofPred_eq, div_lt_iff₀ hR]
    rw [mul_comm]
  simp_rw [hset]
  rw [lintegral_sublevel_swap volume (fun h : Domain n => euclideanLength h / R)
    (euclideanLength_continuous.measurable.div_const R)
    (fun h => div_nonneg (norm_nonneg _) hR.le) F hF
    (fun t : ℝ => ENNReal.ofReal t ^ (-((n : ℝ) + p.toReal)))
    (measurable_id.ennreal_ofReal.pow_const _)]
  calc
    _ = ∫⁻ h, (ENNReal.ofReal R ^ ((n : ℝ) + p.toReal - 1) *
        ENNReal.ofReal (1 / ((n : ℝ) + p.toReal - 1))) *
        (differenceKernel (1 - 1 / p.toReal) p h * F h) := by
      apply lintegral_congr
      intro h
      by_cases hh : h = 0
      · simp [hh, hF0]
      · rw [derivative_scale_kernel_radius p hp1 hp R hR h hh]
        ac_rfl
    _ = _ := lintegral_const_mul _ ((differenceKernel_measurable _ p).mul hF)

lemma euclideanBall_volume {n : ℕ} (r : ℝ) (hr : 0 < r) :
    volume {h : Domain n | euclideanLength h < r} =
      ENNReal.ofReal r ^ n *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  calc
    _ = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) := by
      convert (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
        (show NullMeasurableSet (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) (volume : Measure (EuclideanSpace ℝ (Fin n))) from
          measurableSet_ball.nullMeasurableSet) using 1
      simp only [preimage, Metric.mem_ball, dist_zero_right, mem_ofPred_eq]
      rfl
    _ = _ := by
      rw [Measure.addHaar_ball_of_pos volume _ hr]
      simp only [finrank_euclideanSpace_fin, ENNReal.ofReal_pow hr.le]

lemma scaled_kernel_prefactor (n : ℕ) (q : ℝ) (hq : 1 ≤ q)
    (R M t : ℝ) (hR : 0 < R) (hM : 0 ≤ M) (ht : 0 < t) (V : ℝ≥0∞) :
    (ENNReal.ofReal (R * t) ^ n * V) ^ (q - 1) *
        ENNReal.ofReal (M * (t ^ (n + 1))⁻¹) ^ q =
      ((ENNReal.ofReal R ^ n * V) ^ (q - 1) * ENNReal.ofReal M ^ q) *
        ENNReal.ofReal t ^ (-((n : ℝ) + q)) := by
  have hvol : ENNReal.ofReal (R * t) ^ n * V =
      (ENNReal.ofReal R ^ n * V) * ENNReal.ofReal t ^ n := by
    rw [ENNReal.ofReal_mul hR.le, mul_pow]
    ac_rfl
  have hamp : ENNReal.ofReal (M * (t ^ (n + 1))⁻¹) =
      ENNReal.ofReal M * ENNReal.ofReal t ^ (-(n + 1 : ℕ) : ℝ) := by
    rw [ENNReal.ofReal_mul hM, ENNReal.ofReal_inv_of_pos (pow_pos ht _),
      ENNReal.ofReal_pow ht.le, ENNReal.rpow_neg, ENNReal.rpow_natCast]
  rw [hvol, hamp, ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr hq),
    ENNReal.mul_rpow_of_nonneg _ _ (zero_le_one.trans hq),
    ← ENNReal.rpow_natCast_mul, ← ENNReal.rpow_mul]
  have hexp : (n : ℝ) * (q - 1) + (-(n + 1 : ℕ) : ℝ) * q = -((n : ℝ) + q) := by
    push_cast
    ring
  calc
    _ = ((ENNReal.ofReal R ^ n * V) ^ (q - 1) * ENNReal.ofReal M ^ q) *
        (ENNReal.ofReal t ^ ((n : ℝ) * (q - 1)) *
          ENNReal.ofReal t ^ ((-(n + 1 : ℕ) : ℝ) * q)) := by ac_rfl
    _ = _ := by
      rw [← ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.mpr ht).ne' ENNReal.ofReal_ne_top, hexp]

namespace KernelEstimates

lemma derivativeScaledKernel_energy_bound {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞)
    (K : Domain n → ℝ) (hK : Continuous K) (hKc : HasCompactSupport K)
    (hz : ∫ h, K h = 0) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (𝕜 : Type) [RCLike 𝕜]
      (u : Lp 𝕜 p (volume : Measure (Domain n))) (f : Domain n → 𝕜),
      Continuous f → u =ᵐ[volume] f →
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x,
        ‖∫ h, derivativeScaledKernel K t h • f (x - h)‖ₑ ^ p.toReal) ≤
        C * differenceEnergy (1 - 1 / p.toReal) p u := by
  have hpr : 1 < p.toReal := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).mpr hp1
  obtain ⟨R, M, hR, hM, hb⟩ := derivativeScaledKernel_bounds K hK hKc
  let R' : ℝ := R + 1
  have hR' : 0 < R' := by dsimp [R']; linarith
  let V : ℝ≥0∞ := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
  let A : ℝ≥0∞ := (ENNReal.ofReal R' ^ n * V) ^ (p.toReal - 1) *
    ENNReal.ofReal M ^ p.toReal
  have hA : A ≠ ∞ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) (ENNReal.mul_ne_top (by simp)
        (lt_top_iff_ne_top.mp measure_ball_lt_top)))
      (ENNReal.rpow_ne_top_of_nonneg (zero_le_one.trans hpr.le) ENNReal.ofReal_ne_top)
  let B : ℝ≥0∞ := ENNReal.ofReal R' ^ ((n : ℝ) + p.toReal - 1) *
    ENNReal.ofReal (1 / ((n : ℝ) + p.toReal - 1))
  have hB : B ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]) ENNReal.ofReal_ne_top)
    ENNReal.ofReal_ne_top
  refine ⟨A * B, ENNReal.mul_ne_top hA hB, ?_⟩
  intro 𝕜 _ u f hf huf
  let F := fun h : Domain n => ‖lpIncrement p h u‖ₑ ^ p.toReal
  have hF : Measurable F := (lpIncrement_continuous p hp u).enorm.measurable.pow_const _
  have hF0 : F 0 = 0 := by
    have hi0 : lpIncrement p (0 : Domain n) u = 0 := by
      apply Lp.ext
      filter_upwards [lpIncrement_representative p u (0 : Domain n),
        Lp.coeFn_zero 𝕜 p (volume : Measure (Domain n))] with x hx hz
      simp only [add_zero, sub_self] at hx
      exact hx.trans hz.symm
    simp only [F, hi0, enorm_zero, ENNReal.zero_rpow_of_pos (zero_lt_one.trans hpr)]
  have hpoint (t : ℝ) (ht : 0 < t) :
      (∫⁻ x, ‖∫ h, derivativeScaledKernel K t h • f (x - h)‖ₑ ^ p.toReal) ≤
        A * (ENNReal.ofReal t ^ (-((n : ℝ) + p.toReal)) *
          ∫⁻ h in {h : Domain n | euclideanLength h < R' * t}, F h) := by
    have hs : ∀ h, h ∉ {h : Domain n | euclideanLength h < R' * t} →
        derivativeScaledKernel K t h = 0 := by
      intro h hh
      apply (hb t ht).2 h
      have hlen : R' * t ≤ euclideanLength h := le_of_not_gt hh
      dsimp only [R'] at hlen
      linarith
    have hamp : ∀ᵐ h ∂volume.restrict {h : Domain n | euclideanLength h < R' * t},
        ‖derivativeScaledKernel K t h‖ₑ ≤ ENNReal.ofReal (M * (t ^ (n + 1))⁻¹) := by
      filter_upwards with h
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal ((hb t ht).1 h)
    have hpnt := mean_zero_kernel_increment_bound p hp u f hf huf
      {h : Domain n | euclideanLength h < R' * t} (derivativeScaledKernel K t)
      (derivativeScaledKernel_continuous K hK t)
      (derivativeScaledKernel_hasCompactSupport K hKc ht.ne') hs
      (derivativeScaledKernel_integral_zero K hz ht) _ hamp
    rw [euclideanBall_volume (R' * t) (mul_pos hR' ht),
      scaled_kernel_prefactor n p.toReal hpr.le R' M t hR' hM.le ht V] at hpnt
    simpa only [lpIncrement_enorm_neg, F, mul_assoc, A] using hpnt
  have henergy : (∫⁻ h, differenceKernel (1 - 1 / p.toReal) p h * F h) =
      differenceEnergy (1 - 1 / p.toReal) p u := by
    rw [difference_energy_weighted_integral _ p hp]
    exact (lintegral_withDensity_eq_lintegral_mul _ (differenceKernel_measurable _ p) hF).symm
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), A * (ENNReal.ofReal t ^ (-((n : ℝ) + p.toReal)) *
        ∫⁻ h in {h : Domain n | euclideanLength h < R' * t}, F h) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hpoint t ht
    _ = A * (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal t ^ (-((n : ℝ) + p.toReal)) *
        ∫⁻ h in {h : Domain n | euclideanLength h < R' * t}, F h) :=
      lintegral_const_mul' _ _ hA
    _ = _ := by
      rw [derivative_scale_integral_radius p hp1 hp R' hR' F hF hF0, henergy]
      exact (mul_assoc A B _).symm

end KernelEstimates

namespace SmoothLift
open ExpandedFA.Distributions ExpandedFA.PartIV.FractionalSobolev

/-- The signed-scale average is regular even at height zero for smooth input. -/
def average {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜) (z : Domain n × ℝ) : 𝕜 :=
  ∫ y, ρ y • f (z.1 - z.2 • y)

lemma average_contDiff {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (average ρ f) := by
  let g : (Domain n × ℝ) → Domain n → 𝕜 :=
    fun z y => ρ (-y) • f (z.1 + z.2 • y)
  have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) (Function.uncurry g) := by
    change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun q : (Domain n × ℝ) × Domain n =>
      ρ (-q.2) • f (q.1.1 + q.1.2 • q.2))
    exact (hρ.comp contDiff_snd.neg).smul
      (hf.comp ((contDiff_fst.fst).add (contDiff_fst.snd.smul contDiff_snd)))
  have hgc : IsCompact (tsupport (fun y => ρ (-y))) := by
    exact hρc.comp_isClosedEmbedding (Homeomorph.neg _).isClosedEmbedding
  have hs : ∀ z y, z ∈ (univ : Set (Domain n × ℝ)) →
      y ∉ tsupport (fun y => ρ (-y)) → g z y = 0 := by
    intro z y _ hy
    simp [g, image_eq_zero_of_notMem_tsupport hy]
  have h := contDiffOn_convolution_right_with_param_comp
    (𝕜 := ℝ) (μ := (volume : Measure (Domain n)))
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (v := fun _ : Domain n × ℝ => (0 : Domain n)) contDiffOn_const
    isOpen_univ hgc hs (locallyIntegrable_const (1 : ℝ)) hg.contDiffOn
  rw [contDiffOn_univ] at h
  convert h using 1
  funext z
  simp [average, convolution, g, sub_eq_add_neg]

@[simp] lemma average_zero_height {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜) (hρ : ∫ y, ρ y = 1)
    (x : Domain n) : average ρ f (x, 0) = f x := by
  simp [average, integral_smul_const, hρ]

lemma average_integrable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hf : Continuous f)
    (z : Domain n × ℝ) : Integrable (fun y => ρ y • f (z.1 - z.2 • y)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact hρ.smul (hf.comp (continuous_const.sub (continuous_id.const_smul z.2)))
  · exact hρc.smul_right

/-- A normal cutoff of the signed-scale average. -/
def flatLift {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (z : Domain n × ℝ) : 𝕜 := χ z.2 • average ρ f z

lemma flatLift_contDiff {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (flatLift χ ρ f) :=
  (hχ.comp contDiff_snd).smul (average_contDiff ρ f hρ hρc hf)

@[simp] lemma flatLift_zero_height {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hχ : χ 0 = 1) (hρ : ∫ y, ρ y = 1) (x : Domain n) :
    flatLift χ ρ f (x, 0) = f x := by simp [flatLift, hχ, hρ]

lemma flatLift_hasCompactSupport {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hχc : HasCompactSupport χ) (hρc : HasCompactSupport ρ)
    (hfc : HasCompactSupport f) : HasCompactSupport (flatLift χ ρ f) := by
  obtain ⟨T, hT, hTb⟩ := hχc.isBounded.exists_pos_norm_le
  obtain ⟨R, hR, hRb⟩ := hρc.isBounded.exists_pos_norm_le
  obtain ⟨S, hS, hSb⟩ := hfc.isBounded.exists_pos_norm_le
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Domain n × ℝ) (S + T * R + T))
  intro z hz
  by_cases ht : χ z.2 = 0
  · simp [flatLift, ht]
  · have htS : z.2 ∈ tsupport χ := subset_tsupport _ ht
    have htn : ‖z.2‖ ≤ T := hTb _ htS
    have hxn : S + T * R < ‖z.1‖ := by
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at hz
      have hmax : S + T * R + T < max ‖z.1‖ ‖z.2‖ := lt_of_not_ge hz
      rcases (lt_max_iff.mp hmax) with hx | ht'
      · linarith
      · have hnonneg : 0 ≤ S + T * R := by positivity
        linarith
    have hav : average ρ f z = 0 := by
      apply integral_eq_zero_of_ae
      apply ae_of_all
      intro y
      by_cases hy : ρ y = 0
      · simp [hy]
      · have hyn : ‖y‖ ≤ R := hRb _ (subset_tsupport _ hy)
        have hfz : f (z.1 - z.2 • y) = 0 := by
          by_contra hne
          have hfn : ‖z.1 - z.2 • y‖ ≤ S := hSb _ (subset_tsupport _ hne)
          have hx : ‖z.1‖ ≤ S + T * R := by
            calc
              ‖z.1‖ = ‖(z.1 - z.2 • y) + z.2 • y‖ := by rw [sub_add_cancel]
              _ ≤ ‖z.1 - z.2 • y‖ + ‖z.2 • y‖ := norm_add_le _ _
              _ ≤ S + T * R := by rw [norm_smul]; gcongr
          exact hxn.not_ge hx
        simp [hfz]
    simp [flatLift, hav]

/-- Split off the selected normal coordinate, retaining the canonical Fin n order. -/
def flatCoordinates {n : ℕ} (i : Fin (n + 1)) : Domain (n + 1) ≃ₜ Domain n × ℝ where
  toFun x := (i.removeNth x, x i)
  invFun z := i.insertNth z.2 z.1
  left_inv x := Fin.insertNth_self_removeNth i x
  right_inv := by rintro ⟨x, t⟩; simp
  continuous_toFun := (continuous_pi fun j => continuous_apply (i.succAbove j)).prodMk
    (continuous_apply i)
  continuous_invFun := by
    exact (continuous_snd : Continuous (fun z : Domain n × ℝ => z.2)).finInsertNth i
      (continuous_fst : Continuous (fun z : Domain n × ℝ => z.1))

lemma flatCoordinates_contDiff {n : ℕ} (i : Fin (n + 1)) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (flatCoordinates i) := by
  change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : Domain (n + 1) => (i.removeNth x, x i))
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro j
    change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : Domain (n + 1) => x (i.succAbove j))
    exact contDiff_apply ℝ (fun _ : Fin (n + 1) => ℝ) (i.succAbove j)
  · exact contDiff_apply ℝ (fun _ : Fin (n + 1) => ℝ) i

/-- The lift written in the original upper half-space coordinates. -/
def liftFunction {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (x : Domain (n + 1)) : 𝕜 := flatLift χ ρ f (flatCoordinates i x)

lemma liftFunction_contDiff {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (liftFunction i χ ρ f) :=
  (flatLift_contDiff χ ρ f hχ hρ hρc hf).comp (flatCoordinates_contDiff i)

lemma liftFunction_hasCompactSupport {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hχc : HasCompactSupport χ) (hρc : HasCompactSupport ρ)
    (hfc : HasCompactSupport f) : HasCompactSupport (liftFunction i χ ρ f) :=
  (flatLift_hasCompactSupport χ ρ f hχc hρc hfc).comp_isClosedEmbedding
    (flatCoordinates i).isClosedEmbedding

@[simp] lemma liftFunction_boundary {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hχ : χ 0 = 1) (hρ : ∫ y, ρ y = 1) (x : Domain n) :
    liftFunction i χ ρ f (i.insertNth 0 x) = f x := by
  change flatLift χ ρ f
    (i.removeNth (i.insertNth (α := fun _ : Fin (n + 1) => ℝ) 0 x),
      (i.insertNth (α := fun _ : Fin (n + 1) => ℝ) 0 x) i) = f x
  simp [hχ, hρ]

open ExpandedFA.Sobolev ExpandedFA.Sobolev.HalfSpace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open ExpandedFA.PartIV.SharpTraceBound

/-- The signed-scale formula is an element of the actual full derivative graph.
This assertion records all first derivative representatives as well as order zero. -/
lemma liftFunction_mem_sobolev {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ u : SpaceValue 𝕜 (n + 1) (upper i) 1 p,
      u.val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (upper i : Set (Domain (n + 1)))]
        liftFunction i χ ρ f ∧
      ∀ j, u.val (coordinateIndex j) =ᵐ[volume.restrict (upper i : Set (Domain (n + 1)))]
        fun x => fderiv ℝ (liftFunction i χ ρ f) x (coordinateVector j) := by
  have hF := liftFunction_contDiff i χ ρ f hχ hρ hρc hf
  have hFc := liftFunction_hasCompactSupport i χ ρ f hχc hρc hfc
  apply C1Extension.Classical.c1_mem_sobolev _ (hF.of_le (by simp)).contDiffOn
    (hF.continuous.memLp_of_hasCompactSupport hFc)
  intro j
  exact ((hF.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
    (hFc.fderiv_apply ℝ (coordinateVector j))

/-- Chosen smooth representative, used only after a.e. independence is proved. -/
def representative {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothData 𝕜 n s p) : Domain n → 𝕜 :=
  Classical.choose u.property

lemma representative_contDiff {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothData 𝕜 n s p) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (representative u) :=
  (Classical.choose_spec u.property).1

lemma representative_compactSupport {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothData 𝕜 n s p) :
    HasCompactSupport (representative u) :=
  (Classical.choose_spec u.property).2.1

lemma representative_ae {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothData 𝕜 n s p) :
    u.val.val =ᵐ[volume] representative u :=
  (Classical.choose_spec u.property).2.2

/-- The explicit smoothing formula, inserted into the accepted Sobolev graph. -/
def smoothDataLift {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (u : Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothData 𝕜 n s p) :
    SpaceValue 𝕜 (n + 1) (upper i) 1 p :=
  Classical.choose (liftFunction_mem_sobolev i χ ρ (representative u) hχ hχc hρ hρc
    (representative_contDiff u) (representative_compactSupport u) p)

lemma smoothDataLift_representative {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (u : Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothData 𝕜 n s p) :
    (smoothDataLift i χ ρ hχ hχc hρ hρc u).val (zeroIndex (n + 1) 1) =ᵐ[
      volume.restrict (upper i : Set (Domain (n + 1)))] liftFunction i χ ρ (representative u) :=
  (Classical.choose_spec (liftFunction_mem_sobolev i χ ρ (representative u) hχ hχc hρ hρc
    (representative_contDiff u) (representative_compactSupport u) p)).1

lemma smoothDataLift_derivative {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (u : Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothData 𝕜 n s p) (j : Fin (n + 1)) :
    (smoothDataLift i χ ρ hχ hχc hρ hρc u).val (coordinateIndex j) =ᵐ[
      volume.restrict (upper i : Set (Domain (n + 1)))]
      fun x => fderiv ℝ (liftFunction i χ ρ (representative u)) x (coordinateVector j) :=
  (Classical.choose_spec (liftFunction_mem_sobolev i χ ρ (representative u) hχ hχc hρ hρc
    (representative_contDiff u) (representative_compactSupport u) p)).2 j

lemma smoothDataLift_trace {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hχ0 : χ 0 = 1) (hρmass : ∫ y, ρ y = 1)
    (T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (ExpandedFA.Sobolev.Lines.Transverse i)))
    (hT : CoordinateTraceCondition i T)
    (u : Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothData 𝕜 n s p) :
    reindexedTrace i T (smoothDataLift i χ ρ hχ hχc hρ hρc u) = u.val.val := by
  apply Lp.ext
  have ht := reindexedTrace_smooth i T hT _ _
    ((liftFunction_contDiff i χ ρ (representative u) hχ hρ hρc
      (representative_contDiff u)).of_le (by simp))
    (smoothDataLift_representative i χ ρ hχ hχc hρ hρc u)
  filter_upwards [ht, representative_ae u] with x hx hu
  rw [liftFunction_boundary i χ ρ (representative u) hχ0 hρmass] at hx
  exact hx.trans hu.symm

lemma average_add {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f g : Domain n → 𝕜)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hf : Continuous f) (hg : Continuous g)
    (z : Domain n × ℝ) : average ρ (f + g) z = average ρ f z + average ρ g z := by
  simp only [average, Pi.add_apply, smul_add]
  exact integral_add (average_integrable ρ f hρ hρc hf z) (average_integrable ρ g hρ hρc hg z)

lemma average_smul {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (c : 𝕜) (f : Domain n → 𝕜)
    (z : Domain n × ℝ) : average ρ (c • f) z = c • average ρ f z := by
  simp only [average, Pi.smul_apply, smul_comm (ρ _) c, integral_smul]

lemma liftFunction_add {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f g : Domain n → 𝕜)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hf : Continuous f) (hg : Continuous g)
    (x : Domain (n + 1)) :
    liftFunction i χ ρ (f + g) x = liftFunction i χ ρ f x + liftFunction i χ ρ g x := by
  simp only [liftFunction, flatLift, average_add ρ f g hρ hρc hf hg, smul_add]

lemma liftFunction_smul {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (c : 𝕜) (f : Domain n → 𝕜)
    (x : Domain (n + 1)) :
    liftFunction i χ ρ (c • f) x = c • liftFunction i χ ρ f x := by
  simp only [liftFunction, flatLift, average_smul, smul_comm (χ _) c]

lemma representative_add {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u v w : Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothData 𝕜 n s p)
    (hw : w.val.val = u.val.val + v.val.val) :
    representative w = representative u + representative v := by
  apply Measure.eq_of_ae_eq (μ := (volume : Measure (Domain n))) _
    (representative_contDiff w).continuous
    ((representative_contDiff u).continuous.add (representative_contDiff v).continuous)
  have hwrep := representative_ae w
  rw [hw] at hwrep
  filter_upwards [hwrep, representative_ae u, representative_ae v,
    Lp.coeFn_add u.val.val v.val.val] with x hwx hu hv hadd
  simp only [Pi.add_apply] at hadd
  exact hwx.symm.trans (hadd.trans (congrArg₂ (· + ·) hu hv))

lemma representative_smul {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (c : 𝕜) (u v : Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothData 𝕜 n s p)
    (hv : v.val.val = c • u.val.val) : representative v = c • representative u := by
  apply Measure.eq_of_ae_eq (μ := (volume : Measure (Domain n))) _
    (representative_contDiff v).continuous
    (continuous_const.smul (representative_contDiff u).continuous)
  have hvrep := representative_ae v
  rw [hv] at hvrep
  filter_upwards [hvrep, representative_ae u, Lp.coeFn_smul c u.val.val] with x hvx hu hsmul
  simp only [Pi.smul_apply] at hsmul
  exact hvx.symm.trans (hsmul.trans (congrArg (c • ·) hu))

/-- Algebraic linearity is independent of the representatives and graph choices. -/
lemma smoothDataLift_add {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (u v w : Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothData 𝕜 n s p)
    (hw : w.val.val = u.val.val + v.val.val) :
    smoothDataLift i χ ρ hχ hχc hρ hρc w = smoothDataLift i χ ρ hχ hχc hρ hρc u +
      smoothDataLift i χ ρ hχ hχc hρ hρc v := by
  apply sobolev_underlying_injective 𝕜 (n + 1) (upper i) 1 p
  change (smoothDataLift i χ ρ hχ hχc hρ hρc w).val (zeroIndex (n + 1) 1) =
    (smoothDataLift i χ ρ hχ hχc hρ hρc u).val (zeroIndex (n + 1) 1) +
    (smoothDataLift i χ ρ hχ hχc hρ hρc v).val (zeroIndex (n + 1) 1)
  apply Lp.ext
  filter_upwards [smoothDataLift_representative i χ ρ hχ hχc hρ hρc w,
    smoothDataLift_representative i χ ρ hχ hχc hρ hρc u,
    smoothDataLift_representative i χ ρ hχ hχc hρ hρc v,
    Lp.coeFn_add ((smoothDataLift i χ ρ hχ hχc hρ hρc u).val (zeroIndex (n + 1) 1))
      ((smoothDataLift i χ ρ hχ hχc hρ hρc v).val (zeroIndex (n + 1) 1))]
    with x hwx hu hv hadd
  simp only [Pi.add_apply] at hadd
  rw [hwx, hadd, hu, hv, representative_add u v w hw]
  exact liftFunction_add i χ ρ _ _ hρ.continuous hρc
    (representative_contDiff u).continuous (representative_contDiff v).continuous x

lemma smoothDataLift_smul {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (c : 𝕜) (u v : Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothData 𝕜 n s p)
    (hv : v.val.val = c • u.val.val) :
    smoothDataLift i χ ρ hχ hχc hρ hρc v = c • smoothDataLift i χ ρ hχ hχc hρ hρc u := by
  apply sobolev_underlying_injective 𝕜 (n + 1) (upper i) 1 p
  change (smoothDataLift i χ ρ hχ hχc hρ hρc v).val (zeroIndex (n + 1) 1) =
    c • (smoothDataLift i χ ρ hχ hχc hρ hρc u).val (zeroIndex (n + 1) 1)
  apply Lp.ext
  filter_upwards [smoothDataLift_representative i χ ρ hχ hχc hρ hρc v,
    smoothDataLift_representative i χ ρ hχ hχc hρ hρc u,
    Lp.coeFn_smul c ((smoothDataLift i χ ρ hχ hχc hρ hρc u).val (zeroIndex (n + 1) 1))]
    with x hvx hu hsmul
  simp only [Pi.smul_apply] at hsmul
  rw [hvx, hsmul, hu, representative_smul c u v hv]
  exact liftFunction_smul i χ ρ c _ x

/-- Minkowski bounds each tangential slice by the L1 mass of the fixed kernel. -/
lemma average_eLpNorm_le {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hf : Continuous f)
    (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hfp : MemLp f p volume) (t : ℝ) :
    eLpNorm (fun x => average ρ f (x, t)) p volume ≤
      eLpNorm ρ 1 volume * eLpNorm f p volume := by
  let : MeasurableSpace 𝕜 := borel 𝕜
  let F : Domain n × Domain n → 𝕜 := fun z => ρ z.2 • f (z.1 - t • z.2)
  have hF : Measurable F :=
    (hρ.comp continuous_snd).measurable.smul
      (hf.comp (continuous_fst.sub (continuous_snd.const_smul t))).measurable
  have hρp : MemLp ρ 1 volume := hρ.memLp_of_hasCompactSupport hρc
  have hs (y : Domain n) : eLpNorm (fun x => F (x, y)) p volume =
      ‖ρ y‖ₑ * eLpNorm f p volume := by
    change eLpNorm ((ρ y) • (fun x => f (x - t • y))) p volume = _
    rw [eLpNorm_const_smul]
    exact congrArg (‖ρ y‖ₑ * ·) (eLpNorm_comp_measurePreserving hfp.aestronglyMeasurable
      (measurePreserving_sub_right volume (t • y)))
  have hmass : (∫⁻ y, eLpNorm (fun x => F (x, y)) p volume) =
      eLpNorm ρ 1 volume * eLpNorm f p volume := by
    simp_rw [hs]
    rw [lintegral_mul_const _ hρ.measurable.enorm,
      ← eLpNorm_one_eq_lintegral_enorm hρp.aestronglyMeasurable]
  obtain ⟨_, hb⟩ := minkowski_integral_eLpNorm volume volume p hp1 hp F hF
    (by rw [hmass]; exact ENNReal.mul_lt_top hρp.eLpNorm_lt_top hfp.eLpNorm_lt_top)
  exact hb.trans_eq hmass

lemma flatLift_lintegral_rpow_le {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hfp : MemLp f p volume) :
    (∫⁻ z : Domain n × ℝ, ‖flatLift χ ρ f z‖ₑ ^ p.toReal) ≤
      (∫⁻ t : ℝ, ‖χ t‖ₑ ^ p.toReal) * (eLpNorm ρ 1 volume * eLpNorm f p volume) ^ p.toReal := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp1)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hA := average_contDiff ρ f hρ hρc hf
  have hF := flatLift_contDiff χ ρ f hχ hρ hρc hf
  have hAc (t : ℝ) : Continuous (fun x : Domain n => average ρ f (x, t)) :=
    hA.continuous.comp (continuous_id.prodMk (continuous_const (y := t)))
  have hs (t : ℝ) : (∫⁻ x : Domain n, ‖average ρ f (x, t)‖ₑ ^ p.toReal) ≤
      (eLpNorm ρ 1 volume * eLpNorm f p volume) ^ p.toReal := by
    rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hpr,
      ← eLpNorm_eq_eLpNorm' hp0 hp (hAc t).aestronglyMeasurable]
    exact ENNReal.rpow_le_rpow (average_eLpNorm_le ρ f hρ.continuous hρc hf.continuous
      p hp1 hp hfp t) hpr.le
  calc
    _ = ∫⁻ t : ℝ, ∫⁻ x : Domain n, ‖flatLift χ ρ f (x, t)‖ₑ ^ p.toReal := by
      exact lintegral_prod_symm _ (hF.continuous.enorm.measurable.pow_const _).aemeasurable
    _ = ∫⁻ t : ℝ, ‖χ t‖ₑ ^ p.toReal * ∫⁻ x : Domain n, ‖average ρ f (x, t)‖ₑ ^ p.toReal := by
      apply lintegral_congr
      intro t
      simp only [flatLift, enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ hpr.le]
      rw [lintegral_const_mul _ ((hAc t).enorm.measurable.pow_const _)]
    _ ≤ ∫⁻ t : ℝ, ‖χ t‖ₑ ^ p.toReal *
        (eLpNorm ρ 1 volume * eLpNorm f p volume) ^ p.toReal := by
      apply lintegral_mono
      intro t
      exact mul_le_mul' le_rfl (hs t)
    _ = _ := by rw [lintegral_mul_const _ (hχ.continuous.enorm.measurable.pow_const _)]

lemma flatLift_eLpNorm_le {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hfp : MemLp f p volume) :
    eLpNorm (flatLift χ ρ f) p volume ≤
      eLpNorm χ p volume * eLpNorm ρ 1 volume * eLpNorm f p volume := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp1)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hi : 0 ≤ 1 / p.toReal := (one_div_pos.mpr hpr).le
  have hpow : p.toReal * (1 / p.toReal) = 1 := by field_simp
  rw [mul_assoc]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp
    (flatLift_contDiff χ ρ f hχ hρ hρc hf).continuous.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hχ.continuous.aestronglyMeasurable]
  calc
    _ ≤ ((∫⁻ t : ℝ, ‖χ t‖ₑ ^ p.toReal) *
        (eLpNorm ρ 1 volume * eLpNorm f p volume) ^ p.toReal) ^ (1 / p.toReal) :=
      ENNReal.rpow_le_rpow (flatLift_lintegral_rpow_le χ ρ f hχ hρ hρc hf p hp1 hp hfp) hi
    _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hi, ← ENNReal.rpow_mul, hpow, ENNReal.rpow_one]

lemma flatCoordinates_symm_measurePreserving {n : ℕ} (i : Fin (n + 1)) :
    MeasurePreserving (flatCoordinates i).symm (volume.prod volume) volume := by
  have h := (ExpandedFA.Sobolev.Trace.coordinateUnsplit_measurePreserving i).comp
    ((ExpandedFA.Sobolev.Trace.transverseFinEquiv_measurePreserving i).prod
      (MeasurePreserving.id (volume : Measure ℝ)))
  convert h using 1
  funext z
  exact (ExpandedFA.Sobolev.Trace.coordinateLine_transverseFinEquiv i z.1 z.2).symm

lemma liftFunction_eLpNorm_le {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hfp : MemLp f p volume) :
    eLpNorm (liftFunction i χ ρ f) p (volume.restrict (upper i : Set (Domain (n + 1)))) ≤
      eLpNorm χ p volume * eLpNorm ρ 1 volume * eLpNorm f p volume := by
  apply (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
  have he := eLpNorm_comp_measurePreserving (p := p)
    (liftFunction_contDiff i χ ρ f hχ hρ hρc hf).continuous.aestronglyMeasurable
    (flatCoordinates_symm_measurePreserving i)
  have hfun : liftFunction i χ ρ f ∘ (flatCoordinates i).symm = flatLift χ ρ f := by
    funext z
    simp only [Function.comp_apply, liftFunction, Homeomorph.apply_symm_apply]
  rw [hfun] at he
  have he' : eLpNorm (liftFunction i χ ρ f) p volume = eLpNorm (flatLift χ ρ f) p volume := he.symm

  rw [he']
  exact flatLift_eLpNorm_le χ ρ f hχ hρ hρc hf p hp1 hp hfp

lemma smoothDataLift_zero_norm_le {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hp : p ≠ ∞)
    (u : Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothData 𝕜 n s p) :
    ‖(smoothDataLift i χ ρ hχ hχc hρ hρc u).val (zeroIndex (n + 1) 1)‖ ≤
      (eLpNorm χ p volume).toReal * (eLpNorm ρ 1 volume).toReal * ‖u.val.val‖ := by
  have hχp : MemLp χ p volume := hχ.continuous.memLp_of_hasCompactSupport hχc
  have hρp : MemLp ρ 1 volume := hρ.continuous.memLp_of_hasCompactSupport hρc
  have hfp : MemLp (representative u) p volume :=
    (Lp.memLp u.val.val).ae_eq (representative_ae u)
  have hnorm := liftFunction_eLpNorm_le i χ ρ (representative u) hχ hρ hρc
    (representative_contDiff u) p Fact.out hp hfp
  rw [← eLpNorm_congr_ae (smoothDataLift_representative i χ ρ hχ hχc hρ hρc u),
    ← eLpNorm_congr_ae (representative_ae u), ← Lp.enorm_def, ← Lp.enorm_def] at hnorm
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hχp.eLpNorm_ne_top hρp.eLpNorm_ne_top) (by finiteness))
    hnorm
  simpa only [ENNReal.toReal_mul, toReal_enorm] using hreal


/-- Uniform bounds on order zero and every coordinate derivative bound the
full sum norm of the existing derivative graph. -/
lemma firstJet_norm_le_of_component_bounds {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : SpaceValue 𝕜 d Ω 1 p) (A B N : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hN : 0 ≤ N)
    (hzero : ‖u.val (zeroIndex d 1)‖ ≤ A * N)
    (hpartial : ∀ j, ‖u.val (coordinateIndex j)‖ ≤ B * N) :
    ‖u‖ ≤ (Fintype.card (DerivativeIndex d 1) : ℝ) * (A + B) * N := by
  change ‖u.val‖ ≤ _
  rw [PiLp.norm_eq_of_L1]
  calc
    _ ≤ ∑ _α : DerivativeIndex d 1, (A + B) * N := by
      apply Finset.sum_le_sum
      intro α _
      rcases ExpandedFA.Sobolev.Lines.multiIndex_order_one_cases (natIndex α) α.property with hz | ⟨j, hj⟩
      · have hα : α = zeroIndex d 1 := derivativeIndex_ext hz
        rw [hα]
        exact hzero.trans (by nlinarith)
      · have hα : α = coordinateIndex j := derivativeIndex_ext (by simpa [coordinateIndex] using hj)
        rw [hα]
        exact (hpartial j).trans (by nlinarith)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

lemma smoothDataLift_norm_le_of_partial_bounds {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {s : ℝ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hp : p ≠ ∞) (L : ℝ) (hL : 0 ≤ L)
    (u : Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothData 𝕜 n s p)
    (hpartial : ∀ j, ‖(smoothDataLift i χ ρ hχ hχc hρ hρc u).val (coordinateIndex j)‖ ≤
      L * fractionalNorm s p u.val) :
    ‖smoothDataLift i χ ρ hχ hχc hρ hρc u‖ ≤
      (Fintype.card (DerivativeIndex (n + 1) 1) : ℝ) *
        ((eLpNorm χ p volume).toReal * (eLpNorm ρ 1 volume).toReal + L) * fractionalNorm s p u.val := by
  apply firstJet_norm_le_of_component_bounds _ _ L _ (by positivity) hL
    (fractionalNorm_nonneg s p u.val) _ hpartial
  exact (smoothDataLift_zero_norm_le i χ ρ hχ hχc hρ hρc hp u).trans
    (mul_le_mul_of_nonneg_left (norm_le_fractionalNorm s p u.val) (by positivity))

/-- A fixed normal cutoff, independent of the scalar field and coordinates. -/
def standardCutoff : ℝ → ℝ :=
  (⟨1, 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ))

lemma standardCutoff_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) standardCutoff :=
  ContDiffBump.contDiff _

lemma standardCutoff_compactSupport : HasCompactSupport standardCutoff :=
  ContDiffBump.hasCompactSupport _

@[simp] lemma standardCutoff_zero : standardCutoff 0 = 1 := by
  exact (⟨1, 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ)).one_of_mem_closedBall (by simp)

/-- A fixed positive mass-one tangential mollifier in every dimension. -/
def standardMollifier (n : ℕ) : Domain n → ℝ :=
  (⟨1, 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : Domain n)).normed volume

lemma standardMollifier_contDiff (n : ℕ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (standardMollifier n) :=
  ContDiffBump.contDiff_normed _

lemma standardMollifier_compactSupport (n : ℕ) : HasCompactSupport (standardMollifier n) :=
  ContDiffBump.hasCompactSupport_normed _

lemma standardMollifier_nonneg (n : ℕ) (x : Domain n) : 0 ≤ standardMollifier n x :=
  ContDiffBump.nonneg_normed _ _

@[simp] lemma standardMollifier_integral (n : ℕ) : ∫ y, standardMollifier n y = 1 :=
  ContDiffBump.integral_normed _

@[simp] lemma standardMollifier_eLpNorm_one (n : ℕ) : eLpNorm (standardMollifier n) 1 volume = 1 := by
  rw [eLpNorm_one_eq_lintegral_enorm (standardMollifier_contDiff n).continuous.aestronglyMeasurable]
  simp_rw [← ofReal_norm, Real.norm_of_nonneg (standardMollifier_nonneg n _)]
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((standardMollifier_contDiff n).continuous.integrable_of_hasCompactSupport
      (standardMollifier_compactSupport n)) (ae_of_all _ (standardMollifier_nonneg n)),
    standardMollifier_integral]
  simp

/-- The geometric construction with these fixed kernels. -/
abbrev canonicalLift {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (i : Fin (n + 1)) :=
  smoothDataLift (𝕜 := 𝕜) (s := s) (p := p) i standardCutoff (standardMollifier n)
    standardCutoff_contDiff standardCutoff_compactSupport
    (standardMollifier_contDiff n) (standardMollifier_compactSupport n)

/-- After the coordinate derivative estimates, all geometric and functional
analytic clauses of the smooth right inverse follow from this construction. -/
theorem smooth_right_inverse_of_canonical_partial_bounds
    (hpartial : ∀ (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
      ∃ L : ℝ, 0 ≤ L ∧ ∀ (𝕜 : Type) [RCLike 𝕜] (i : Fin (n + 1))
        (u : Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothData 𝕜 n (1 - 1 / p.toReal) p)
        (j : Fin (n + 1)),
        ‖(canonicalLift i u).val (coordinateIndex j)‖ ≤
          L * fractionalNorm (1 - 1 / p.toReal) p u.val) :
    Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothRightInverse := by
  intro n p _ hp1 hp
  obtain ⟨L, hL, hpart⟩ := hpartial n p hp1 hp
  let A := (eLpNorm standardCutoff p volume).toReal
  let C := (Fintype.card (DerivativeIndex (n + 1) 1) : ℝ) * (A + L)
  refine ⟨C, by dsimp [C, A]; positivity, ?_⟩
  intro 𝕜 _ i
  refine ⟨canonicalLift i, ?_, ?_, ?_, ?_⟩
  · intro u v w hw
    exact smoothDataLift_add i standardCutoff (standardMollifier n)
      standardCutoff_contDiff standardCutoff_compactSupport
      (standardMollifier_contDiff n) (standardMollifier_compactSupport n) u v w hw
  · intro c u v hv
    exact smoothDataLift_smul i standardCutoff (standardMollifier n)
      standardCutoff_contDiff standardCutoff_compactSupport
      (standardMollifier_contDiff n) (standardMollifier_compactSupport n) c u v hv
  · intro u
    simpa only [standardMollifier_eLpNorm_one, ENNReal.toReal_one, mul_one] using
      smoothDataLift_norm_le_of_partial_bounds i standardCutoff (standardMollifier n)
        standardCutoff_contDiff standardCutoff_compactSupport
        (standardMollifier_contDiff n) (standardMollifier_compactSupport n) hp L hL u
        (hpart 𝕜 i u)
  · intro T hT u
    exact smoothDataLift_trace i standardCutoff (standardMollifier n)
      standardCutoff_contDiff standardCutoff_compactSupport
      (standardMollifier_contDiff n) (standardMollifier_compactSupport n)
      standardCutoff_zero (standardMollifier_integral n) T hT u

/-- The cutoff product-rule term is controlled entirely by the input Lp norm. -/
lemma cutoff_derivative_eLpNorm_le {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hfp : MemLp f p volume) :
    eLpNorm (fun x : Domain (n + 1) => deriv χ (x i) •
      average ρ f (flatCoordinates i x)) p
      (volume.restrict (upper i : Set (Domain (n + 1)))) ≤
        eLpNorm (deriv χ) p volume * eLpNorm ρ 1 volume * eLpNorm f p volume := by
  have hχ' : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv χ) := by
    exact (hχ.fderiv_right (by simp)).clm_apply contDiff_const
  exact liftFunction_eLpNorm_le i (deriv χ) ρ f hχ' hρ hρc hf p hp1 hp hfp


def flatCoordinatesCLM {n : ℕ} (i : Fin (n + 1)) :
    Domain (n + 1) →L[ℝ] Domain n × ℝ :=
  (ContinuousLinearMap.pi fun j =>
    (ContinuousLinearMap.proj (i.succAbove j) : Domain (n + 1) →L[ℝ] ℝ)).prod
      (ContinuousLinearMap.proj i)

@[simp] lemma flatCoordinatesCLM_apply {n : ℕ} (i : Fin (n + 1)) (x : Domain (n + 1)) :
    flatCoordinatesCLM i x = flatCoordinates i x := rfl

@[simp] lemma flatCoordinatesCLM_normal {n : ℕ} (i : Fin (n + 1)) :
    flatCoordinatesCLM i (coordinateVector i) = (0, 1) := by
  ext j
  · simp [flatCoordinatesCLM, coordinateVector, Fin.succAbove_ne]
  · simp [flatCoordinatesCLM, coordinateVector]

@[simp] lemma flatCoordinatesCLM_tangential {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    flatCoordinatesCLM i (coordinateVector (i.succAbove j)) = (coordinateVector j, 0) := by
  ext k
  · simp [flatCoordinatesCLM, coordinateVector, Pi.single_apply,
      Fin.succAbove_right_injective.eq_iff]
  · simp [flatCoordinatesCLM, coordinateVector, Pi.single_apply]

lemma liftFunction_fderiv_coordinates {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (x v : Domain (n + 1)) :
    fderiv ℝ (liftFunction i χ ρ f) x v =
      fderiv ℝ (flatLift χ ρ f) (flatCoordinates i x) (flatCoordinatesCLM i v) := by
  have hF := flatLift_contDiff χ ρ f hχ hρ hρc hf
  have hd := (hF.differentiable (by simp) (flatCoordinates i x)).hasFDerivAt.comp x
    (flatCoordinatesCLM i).hasFDerivAt
  change HasFDerivAt (liftFunction i χ ρ f) _ x at hd
  rw [hd.fderiv]
  rfl

lemma flatLift_fderiv_tangential {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (z : Domain n × ℝ) (v : Domain n) :
    fderiv ℝ (flatLift χ ρ f) z (v, 0) =
      χ z.2 • fderiv ℝ (average ρ f) z (v, 0) := by
  have hχc := (hχ.differentiable (by simp) z.2).hasFDerivAt.comp z
    (ContinuousLinearMap.snd ℝ (Domain n) ℝ).hasFDerivAt
  change HasFDerivAt (fun z : Domain n × ℝ => χ z.2) _ z at hχc
  have hA := (average_contDiff ρ f hρ hρc hf).differentiable (by simp) z
  change fderiv ℝ (fun z : Domain n × ℝ => χ z.2 • average ρ f z) z (v, 0) = _
  rw [fderiv_fun_smul hχc.differentiableAt hA, hχc.fderiv]
  simp

lemma flatLift_fderiv_normal {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (z : Domain n × ℝ) :
    fderiv ℝ (flatLift χ ρ f) z (0, 1) =
      χ z.2 • fderiv ℝ (average ρ f) z (0, 1) +
        deriv χ z.2 • average ρ f z := by
  have hχc := (hχ.differentiable (by simp) z.2).hasFDerivAt.comp z
    (ContinuousLinearMap.snd ℝ (Domain n) ℝ).hasFDerivAt
  change HasFDerivAt (fun z : Domain n × ℝ => χ z.2) _ z at hχc
  have hA := (average_contDiff ρ f hρ hρc hf).differentiable (by simp) z
  change fderiv ℝ (fun z : Domain n × ℝ => χ z.2 • average ρ f z) z (0, 1) = _
  rw [fderiv_fun_smul hχc.differentiableAt hA, hχc.fderiv]
  simp


lemma average_fderiv_spatial {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (z : Domain n × ℝ) (v : Domain n) :
    fderiv ℝ (average ρ f) z (v, 0) =
      fderiv ℝ (fun x => average ρ f (x, z.2)) z.1 v := by
  have hA := (average_contDiff ρ f hρ hρc hf).differentiable (by simp) z
  have hpair : HasFDerivAt (fun x : Domain n => (x, z.2))
      ((ContinuousLinearMap.id ℝ (Domain n)).prod (0 : Domain n →L[ℝ] ℝ)) z.1 :=
    (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1)
  have hd := hA.hasFDerivAt.comp z.1 hpair
  change HasFDerivAt (fun x => average ρ f (x, z.2)) _ z.1 at hd
  rw [hd.fderiv]
  simp

lemma average_fderiv_normal {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (z : Domain n × ℝ) :
    fderiv ℝ (average ρ f) z (0, 1) =
      deriv (fun t => average ρ f (z.1, t)) z.2 := by
  have hA := (average_contDiff ρ f hρ hρc hf).differentiable (by simp) z
  have hpair : HasFDerivAt (fun t : ℝ => (z.1, t))
      ((0 : ℝ →L[ℝ] Domain n).prod (ContinuousLinearMap.id ℝ ℝ)) z.2 :=
    (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)
  have hd := hA.hasFDerivAt.comp z.2 hpair
  change HasFDerivAt (fun t => average ρ f (z.1, t)) _ z.2 at hd
  rw [hd.hasDerivAt.deriv]
  simp

lemma liftFunction_fderiv_tangential {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (x : Domain (n + 1)) (j : Fin n) :
    fderiv ℝ (liftFunction i χ ρ f) x (coordinateVector (i.succAbove j)) =
      χ (x i) • fderiv ℝ (fun y => average ρ f (y, x i))
        (i.removeNth x) (coordinateVector j) := by
  rw [liftFunction_fderiv_coordinates i χ ρ f hχ hρ hρc hf,
    flatCoordinatesCLM_tangential, flatLift_fderiv_tangential χ ρ f hχ hρ hρc hf,
    average_fderiv_spatial ρ f hρ hρc hf]
  rfl

lemma liftFunction_fderiv_normal {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (x : Domain (n + 1)) :
    fderiv ℝ (liftFunction i χ ρ f) x (coordinateVector i) =
      χ (x i) • deriv (fun t => average ρ f (i.removeNth x, t)) (x i) +
        deriv χ (x i) • average ρ f (i.removeNth x, x i) := by
  rw [liftFunction_fderiv_coordinates i χ ρ f hχ hρ hρc hf,
    flatCoordinatesCLM_normal, flatLift_fderiv_normal χ ρ f hχ hρ hρc hf,
    average_fderiv_normal ρ f hρ hρc hf]
  rfl


lemma average_fderiv_spatial_kernel {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (z : Domain n × ℝ) (hz : 0 < z.2) (v : Domain n) :
    fderiv ℝ (average ρ f) z (v, 0) =
      ∫ y, ((z.2 ^ n)⁻¹ * z.2⁻¹ * fderiv ℝ ρ (z.2⁻¹ • y) v) • f (z.1 - y) := by
  rw [average_fderiv_spatial ρ f hρ hρc hf]
  have heq : (fun x => average ρ f (x, z.2)) =
      ExpandedFA.Distributions.SmoothApproximateIdentitiesSpec.MollifyValue ρ z.2 f := by
    funext x
    exact (mollify_eq_signed_average ρ f z.2 hz x).symm
  rw [heq]
  exact scaledKernel_convolution_directional_formula ρ hρc (hρ.of_le (by simp)) f
    (hf.continuous.locallyIntegrable) z.2 hz.ne' z.1 v

lemma liftFunction_fderiv_tangential_kernel {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (x : Domain (n + 1)) (hx : 0 < x i) (j : Fin n) :
    fderiv ℝ (liftFunction i χ ρ f) x (coordinateVector (i.succAbove j)) =
      χ (x i) • convolution
        (KernelEstimates.derivativeScaledKernel (fun y => fderiv ℝ ρ y (coordinateVector j)) (x i))
        f (ContinuousLinearMap.lsmul ℝ ℝ) volume (i.removeNth x) := by
  rw [liftFunction_fderiv_coordinates i χ ρ f hχ hρ hρc hf,
    flatCoordinatesCLM_tangential, flatLift_fderiv_tangential χ ρ f hχ hρ hρc hf,
    average_fderiv_spatial_kernel ρ f hρ hρc hf _ hx]
  congr 1
  change (∫ y, ((x i ^ n)⁻¹ * (x i)⁻¹ * fderiv ℝ ρ ((x i)⁻¹ • y) (coordinateVector j)) •
    f (i.removeNth x - y)) = _
  simp only [convolution, KernelEstimates.derivativeScaledKernel, pow_succ, mul_inv_rev]
  congr 1
  funext y
  congr 1
  ring


lemma average_hasDerivAt_normal {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (x : Domain n) (t : ℝ) :
    HasDerivAt (fun r : ℝ => average ρ f (x,r))
      (∫ z, ρ z • fderiv ℝ f (x - t • z) (-z)) t := by
  obtain ⟨M, hM⟩ := (hfc.fderiv ℝ).exists_bound_of_continuous
    (hf.continuous_fderiv one_ne_zero)
  let F : ℝ → Domain n → 𝕜 := fun r z => ρ z • f (x - r • z)
  let F' : ℝ → Domain n → 𝕜 := fun r z => ρ z • fderiv ℝ f (x - r • z) (-z)
  let B : Domain n → ℝ := fun z => ‖ρ z‖ * M * ‖z‖
  have hF (r : ℝ) : Continuous (F r) := by dsimp [F]; fun_prop
  have hF' (r : ℝ) : Continuous (F' r) := by
    have hs : Continuous (fun z : Domain n => x - r • z) := by fun_prop
    exact hρ.smul (((hf.continuous_fderiv one_ne_zero).comp hs).clm_apply continuous_id.neg)
  have hBi : Integrable B := by
    apply ((hρ.norm.mul continuous_const).mul continuous_norm).integrable_of_hasCompactSupport
    exact hρc.norm.mul_right.mul_right
  have hbd : ∀ᵐ z ∂volume, ∀ r ∈ (univ : Set ℝ), ‖F' r z‖ ≤ B z := by
    filter_upwards with z r hr
    dsimp [F', B]
    rw [norm_smul]
    simp only [Real.norm_eq_abs, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    simpa only [norm_neg, mul_assoc] using
      ((fderiv ℝ f (x - r • z)).le_opNorm (-z)).trans
        (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
  have hdiff : ∀ᵐ z ∂volume, ∀ r ∈ (univ : Set ℝ), HasDerivAt (F · z) (F' r z) r := by
    filter_upwards with z r hr
    simpa only [F, F', Function.comp_def, Pi.smul_def, Pi.smul_apply, Pi.sub_apply, id_eq, one_smul, zero_sub] using
      (((hf.differentiable_one _).hasFDerivAt).comp_hasDerivAt r
        ((hasDerivAt_const r x).sub ((hasDerivAt_id r).smul_const z))).const_smul (ρ z)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (s := univ) (μ := volume) (bound := B) (x₀ := t)
    (univ_mem) (Eventually.of_forall fun r => (hF r).aestronglyMeasurable)
    ((hF t).integrable_of_hasCompactSupport hρc.smul_right)
    (hF' t).aestronglyMeasurable hbd hBi hdiff
  exact h.2
open KernelEstimates in
lemma normalKernel_integral_smul {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (g : Domain n → 𝕜)
    (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ)
    (hg : ContDiff ℝ 1 g) :
    (∫ z, normalKernel ρ z • g z) = ∫ z, ρ z • fderiv ℝ g z z := by
  let a (j : Fin n) : Domain n → ℝ := fun z => z j * ρ z
  let b (j : Fin n) : Domain n → ℝ := fun z => ρ z + z j * fderiv ℝ ρ z (Pi.single j 1)
  have hac (j : Fin n) : HasCompactSupport (a j) := hρc.mul_left
  have had (j : Fin n) : ContDiff ℝ 1 (a j) := (ContinuousLinearMap.proj j : Domain n →L[ℝ] ℝ).contDiff.mul hρ
  have hb (j : Fin n) : Continuous (b j) := hρ.continuous.add ((continuous_apply j).mul
    ((hρ.continuous_fderiv one_ne_zero).clm_apply continuous_const))
  have hadv (j : Fin n) (z : Domain n) :
      fderiv ℝ (a j) z (Pi.single j 1) = b j z := by
    have hi := ((ContinuousLinearMap.proj j : Domain n →L[ℝ] ℝ).hasFDerivAt.mul
      (hρ.differentiable_one z).hasFDerivAt).fderiv
    change fderiv ℝ (((ContinuousLinearMap.proj j : Domain n →L[ℝ] ℝ) : Domain n → ℝ) * ρ) z (Pi.single j 1) = _
    rw [hi]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, Pi.single_eq_same, one_smul, smul_eq_mul, b]
    ring
  have hbc (j : Fin n) : HasCompactSupport (b j) := by
    have heq : b j = fun z => fderiv ℝ (a j) z (Pi.single j 1) := funext fun z => (hadv j z).symm
    rw [heq]
    exact (hac j).fderiv_apply ℝ (Pi.single j 1)
  have hi (j : Fin n) : Integrable (fun z => a j z • fderiv ℝ g z (Pi.single j 1)) :=
    ((had j).continuous.smul ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hac j).smul_right
  have hbi (j : Fin n) : Integrable (fun z => b j z • g z) :=
    ((hb j).smul hg.continuous).integrable_of_hasCompactSupport (hbc j).smul_right
  have hparts (j : Fin n) : (∫ z, a j z • fderiv ℝ g z (Pi.single j 1)) =
      -(∫ z, b j z • g z) := by
    have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
      (f := a j) (g := g) (v := Pi.single j 1)
      (by simpa only [hadv] using hbi j) (hi j)
      (((had j).continuous.smul hg.continuous).integrable_of_hasCompactSupport (hac j).smul_right)
      (fun z _ => (had j).differentiable_one z) (fun z _ => hg.differentiable_one z)
    simpa only [hadv] using h
  have hleft (z : Domain n) : normalKernel ρ z • g z = -(∑ j : Fin n, b j z • g z) := by
    have hd : fderiv ℝ ρ z z = ∑ j : Fin n, z j * fderiv ℝ ρ z (Pi.single j 1) := by
      calc
        _ = fderiv ℝ ρ z (∑ j, z j • Pi.single j 1) := congrArg _ (pi_eq_sum_univ' z)
        _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
    simp only [b, add_smul, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, ← Finset.sum_smul, normalKernel, hd]
    simp only [sub_smul, neg_mul, neg_smul, neg_add_rev, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    abel
  have hright (z : Domain n) : (∑ j : Fin n, a j z • fderiv ℝ g z (Pi.single j 1)) =
      ρ z • fderiv ℝ g z z := by
    have hdg : fderiv ℝ g z z = ∑ j : Fin n, z j • fderiv ℝ g z (Pi.single j 1) := by
      calc
        _ = fderiv ℝ g z (∑ j, z j • Pi.single j 1) := congrArg _ (pi_eq_sum_univ' z)
        _ = _ := by simp only [map_sum, map_smul]
    rw [hdg, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [a]
    rw [smul_smul, mul_comm]
  calc
    _ = ∫ z, -(∑ j : Fin n, b j z • g z) := integral_congr_ae (Eventually.of_forall hleft)
    _ = -(∑ j : Fin n, ∫ z, b j z • g z) := by
      rw [integral_neg, integral_finsetSum _ (fun j _ => hbi j)]
    _ = ∑ j : Fin n, ∫ z, a j z • fderiv ℝ g z (Pi.single j 1) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun j _ => (hparts j).symm)
    _ = _ := by
      rw [← integral_finsetSum _ (fun j _ => hi j)]
      exact integral_congr_ae (Eventually.of_forall hright)
open KernelEstimates in
lemma normalKernel_average_derivative_identity {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ 1 f) (x : Domain n) (t : ℝ) :
    (∫ z, normalKernel ρ z • f (x - t • z)) =
      t • ∫ z, ρ z • fderiv ℝ f (x - t • z) (-z) := by
  let g : Domain n → 𝕜 := fun z => f (x - t • z)
  have hg : ContDiff ℝ 1 g := hf.comp (contDiff_const.sub (contDiff_id.const_smul t))
  have hd (z : Domain n) : fderiv ℝ g z z = t • fderiv ℝ f (x - t • z) (-z) := by
    have h := ((hf.differentiable_one _).hasFDerivAt).comp z
      ((hasFDerivAt_const x z).sub ((hasFDerivAt_id z).const_smul t))
    change HasFDerivAt g _ z at h
    rw [h.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.id_apply, Pi.sub_apply, Pi.smul_apply, id_eq, zero_sub,
      map_neg, map_smul, smul_neg]
  calc
    _ = ∫ z, ρ z • fderiv ℝ g z z := normalKernel_integral_smul ρ g hρ hρc hg
    _ = ∫ z, t • (ρ z • fderiv ℝ f (x - t • z) (-z)) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [hd, smul_comm]
    _ = _ := integral_smul _ _

open KernelEstimates in
lemma average_hasDerivAt_normalKernel {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (x : Domain n) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun r : ℝ => average ρ f (x,r))
      (t⁻¹ • ∫ z, normalKernel ρ z • f (x - t • z)) t := by
  rw [normalKernel_average_derivative_identity ρ f hρ hρc hf x t, smul_smul, inv_mul_cancel₀ ht,
    one_smul]
  exact average_hasDerivAt_normal ρ f hρ.continuous hρc hf hfc x t
open KernelEstimates in
lemma derivativeScaledKernel_integral_smul_eq {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (K : Domain n → ℝ) (f : Domain n → 𝕜) (x : Domain n) {t : ℝ} (ht : 0 < t) :
    (∫ h, derivativeScaledKernel K t h • f (x-h)) =
      t⁻¹ • ∫ z, K z • f (x-t • z) := by
  have hscale : (∫ h, K (t⁻¹ • h) • f (x-h)) =
      t ^ n • ∫ z, K z • f (x-t • z) := by
    have h := Measure.integral_comp_inv_smul_of_nonneg volume
      (fun z => K z • f (x-t • z)) ht.le
    simp only [Module.finrank_pi, Fintype.card_fin] at h
    convert h using 1
    apply integral_congr_ae
    filter_upwards with h
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  calc
    _ = (t ^ (n + 1))⁻¹ • ∫ h, K (t⁻¹ • h) • f (x-h) := by
      simp only [derivativeScaledKernel, mul_smul, integral_smul]
    _ = _ := by
      rw [hscale, smul_smul]
      congr 1
      rw [pow_succ]
      field_simp

open KernelEstimates in
lemma average_hasDerivAt_normal_convolution {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (x : Domain n) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun r : ℝ => average ρ f (x,r))
      (convolution (derivativeScaledKernel (normalKernel ρ) t) f
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x) t := by
  change HasDerivAt _ (∫ h, derivativeScaledKernel (normalKernel ρ) t h • f (x-h)) t
  rw [derivativeScaledKernel_integral_smul_eq _ _ _ ht]
  exact average_hasDerivAt_normalKernel ρ f hρ hρc hf hfc x ht.ne'

open KernelEstimates in
lemma average_deriv_normal_formula {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (x : Domain n) {t : ℝ} (ht : 0 < t) :
    deriv (fun r : ℝ => average ρ f (x,r)) t =
      convolution (derivativeScaledKernel (normalKernel ρ) t) f
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x :=
  (average_hasDerivAt_normal_convolution ρ f hρ hρc hf hfc x ht).deriv

/-- Reindexed normal/tangential integration on the actual coordinate upper half-space. -/
lemma upper_lintegral_flatCoordinates {n : ℕ} (i : Fin (n + 1))
    (H : Domain n × ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ x in (upper i : Set (Domain (n + 1))), H (flatCoordinates i x)) =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ y : Domain n, H (y, t) := by
  have hpre : (flatCoordinates i).symm ⁻¹' (upper i : Set (Domain (n + 1))) =
      univ ×ˢ Ioi (0 : ℝ) := by
    ext z
    change 0 < (i.insertNth (α := fun _ : Fin (n + 1) => ℝ) z.2 z.1) i ↔ _
    simp
  have hm := (flatCoordinates_symm_measurePreserving i).setLIntegral_comp_preimage
    (upper i).isOpen.measurableSet (hH.comp (flatCoordinates i).continuous.measurable)
  rw [hpre, ← Measure.prod_restrict, Measure.restrict_univ] at hm
  simp only [Function.comp_apply, Homeomorph.apply_symm_apply] at hm
  rw [← hm]

  exact lintegral_prod_symm H hH.aemeasurable

/-- A finite p-th-power energy bound gives a uniform norm estimate in the
original Lp component, with the full fractional norm on the datum. -/
lemma lp_norm_le_fractionalNorm_of_energy_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (s : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (v : Lp 𝕜 p μ) (u : FractionalSpace 𝕜 n s p)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hbound : (∫⁻ x, ‖v x‖ₑ ^ p.toReal ∂μ) ≤ C * differenceEnergy s p u.val) :
    ‖v‖ ≤ C.toReal ^ (1 / p.toReal) * fractionalNorm s p u := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hi : 0 ≤ 1 / p.toReal := (one_div_pos.mpr hpr).le
  have he : ‖v‖ₑ ≤ C ^ (1 / p.toReal) * differenceEnergy s p u.val ^ (1 / p.toReal) := by
    rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (Lp.memLp v).aestronglyMeasurable]
    calc
      _ ≤ (C * differenceEnergy s p u.val) ^ (1 / p.toReal) := ENNReal.rpow_le_rpow hbound hi
      _ = _ := ENNReal.mul_rpow_of_nonneg _ _ hi
  have hfin : C ^ (1 / p.toReal) * differenceEnergy s p u.val ^ (1 / p.toReal) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hi hC)
      (ENNReal.rpow_ne_top_of_nonneg hi u.property.ne)
  have hreal := ENNReal.toReal_mono hfin he
  simp only [toReal_enorm, ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at hreal
  apply hreal.trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  exact le_add_of_nonneg_left (norm_nonneg u.val)

/-- A measurable flat expression for a classical derivative, together with
its integrated energy bound, controls the corresponding actual graph component. -/
lemma smoothDataLift_partial_norm_le_of_flat_energy {𝕜 : Type} [RCLike 𝕜]
    {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hp : p ≠ ∞)
    (u : Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothData 𝕜 n s p)
    (j : Fin (n + 1)) (D : Domain n × ℝ → 𝕜)
    (hD : Measurable (fun z => ‖D z‖ₑ ^ p.toReal))
    (hformula : ∀ x, 0 < x i →
      fderiv ℝ (liftFunction i χ ρ (representative u)) x (coordinateVector j) =
        D (flatCoordinates i x))
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hbound : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ y : Domain n, ‖D (y, t)‖ₑ ^ p.toReal) ≤
      C * differenceEnergy s p u.val.val) :
    ‖(smoothDataLift i χ ρ hχ hχc hρ hρc u).val (coordinateIndex j)‖ ≤
      C.toReal ^ (1 / p.toReal) * fractionalNorm s p u.val := by
  apply lp_norm_le_fractionalNorm_of_energy_bound _ s p hp _ u.val C hC
  have he : (∫⁻ x in (upper i : Set (Domain (n + 1))),
      ‖(smoothDataLift i χ ρ hχ hχc hρ hρc u).val (coordinateIndex j) x‖ₑ ^ p.toReal) =
      ∫⁻ x in (upper i : Set (Domain (n + 1))), ‖D (flatCoordinates i x)‖ₑ ^ p.toReal := by
    apply lintegral_congr_ae
    filter_upwards [smoothDataLift_derivative i χ ρ hχ hχc hρ hρc u j,
      ae_restrict_mem (upper i).isOpen.measurableSet] with x hx hxi
    rw [hx, hformula x hxi]
  rw [he, upper_lintegral_flatCoordinates i _ hD]
  exact hbound

lemma differenceEnergy_le_fractionalNorm_rpow {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : FractionalSpace 𝕜 n s p) :
    differenceEnergy s p u.val ≤ ENNReal.ofReal (fractionalNorm s p u) ^ p.toReal := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hi : 0 ≤ 1 / p.toReal := (one_div_pos.mpr hpr).le
  have hroot : differenceEnergy s p u.val ^ (1 / p.toReal) ≤
      ENNReal.ofReal (fractionalNorm s p u) := by
    calc
      _ = ENNReal.ofReal ((differenceEnergy s p u.val ^ (1 / p.toReal)).toReal) :=
        (ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg hi u.property.ne)).symm
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [← ENNReal.toReal_rpow]
        exact le_add_of_nonneg_left (norm_nonneg u.val)
  have hpow := ENNReal.rpow_le_rpow hroot hpr.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hpr.ne', ENNReal.rpow_one] at hpow
  exact hpow

/-- Numeric passage from a p-th-power bound to a real Lp norm bound. -/
lemma lp_norm_le_of_lintegral_rpow_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (v : Lp 𝕜 p μ) (C : ℝ≥0∞) (hC : C ≠ ∞) (N : ℝ) (hN : 0 ≤ N)
    (hbound : (∫⁻ x, ‖v x‖ₑ ^ p.toReal ∂μ) ≤ C * ENNReal.ofReal N ^ p.toReal) :
    ‖v‖ ≤ C.toReal ^ (1 / p.toReal) * N := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hi : 0 ≤ 1 / p.toReal := (one_div_pos.mpr hpr).le
  have hpow : p.toReal * (1 / p.toReal) = 1 := by field_simp
  have he : ‖v‖ₑ ≤ C ^ (1 / p.toReal) * ENNReal.ofReal N := by
    rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (Lp.memLp v).aestronglyMeasurable]
    calc
      _ ≤ (C * ENNReal.ofReal N ^ p.toReal) ^ (1 / p.toReal) := ENNReal.rpow_le_rpow hbound hi
      _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hi, ← ENNReal.rpow_mul, hpow, ENNReal.rpow_one]
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hi hC) ENNReal.ofReal_ne_top) he
  simpa only [toReal_enorm, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hN] using hreal

lemma smoothDataLift_partial_norm_le_of_flat_bound {𝕜 : Type} [RCLike 𝕜]
    {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hp : p ≠ ∞)
    (u : Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothData 𝕜 n s p)
    (j : Fin (n + 1)) (D : Domain n × ℝ → 𝕜)
    (hD : Measurable (fun z => ‖D z‖ₑ ^ p.toReal))
    (hformula : ∀ x, 0 < x i →
      fderiv ℝ (liftFunction i χ ρ (representative u)) x (coordinateVector j) =
        D (flatCoordinates i x))
    (C : ℝ≥0∞) (hC : C ≠ ∞) (N : ℝ) (hN : 0 ≤ N)
    (hbound : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ y : Domain n, ‖D (y, t)‖ₑ ^ p.toReal) ≤
      C * ENNReal.ofReal N ^ p.toReal) :
    ‖(smoothDataLift i χ ρ hχ hχc hρ hρc u).val (coordinateIndex j)‖ ≤
      C.toReal ^ (1 / p.toReal) * N := by
  apply lp_norm_le_of_lintegral_rpow_bound _ p hp _ C hC N hN
  have he : (∫⁻ x in (upper i : Set (Domain (n + 1))),
      ‖(smoothDataLift i χ ρ hχ hχc hρ hρc u).val (coordinateIndex j) x‖ₑ ^ p.toReal) =
      ∫⁻ x in (upper i : Set (Domain (n + 1))), ‖D (flatCoordinates i x)‖ₑ ^ p.toReal := by
    apply lintegral_congr_ae
    filter_upwards [smoothDataLift_derivative i χ ρ hχ hχc hρ hρc u j,
      ae_restrict_mem (upper i).isOpen.measurableSet] with x hx hxi
    rw [hx, hformula x hxi]
  rw [he, upper_lintegral_flatCoordinates i _ hD]
  exact hbound


lemma canonical_cutoff_flat_power_bound {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {s : ℝ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothData 𝕜 n s p) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ y : Domain n,
      ‖deriv standardCutoff t • average (standardMollifier n) (representative u) (y, t)‖ₑ ^ p.toReal) ≤
      eLpNorm (deriv standardCutoff) p volume ^ p.toReal *
        ENNReal.ofReal (fractionalNorm s p u.val) ^ p.toReal := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hχd : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv standardCutoff) := by
    exact (standardCutoff_contDiff.fderiv_right (by simp)).clm_apply contDiff_const
  have hfp : MemLp (representative u) p volume :=
    (Lp.memLp u.val.val).ae_eq (representative_ae u)
  have hF := flatLift_contDiff (deriv standardCutoff) (standardMollifier n) (representative u)
    hχd (standardMollifier_contDiff n) (standardMollifier_compactSupport n) (representative_contDiff u)
  have hmass : (∫⁻ t : ℝ, ‖deriv standardCutoff t‖ₑ ^ p.toReal) =
      eLpNorm (deriv standardCutoff) p volume ^ p.toReal := by
    rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hpr,
      ← eLpNorm_eq_eLpNorm' hp0 hp hχd.continuous.aestronglyMeasurable]
  have hrepnorm : eLpNorm (representative u) p volume = ‖u.val.val‖ₑ := by
    rw [← eLpNorm_congr_ae (representative_ae u), Lp.enorm_def]
  calc
    _ ≤ ∫⁻ t : ℝ, ∫⁻ y : Domain n,
        ‖deriv standardCutoff t • average (standardMollifier n) (representative u) (y, t)‖ₑ ^ p.toReal :=
      setLIntegral_le_lintegral _ _
    _ = ∫⁻ z : Domain n × ℝ,
        ‖flatLift (deriv standardCutoff) (standardMollifier n) (representative u) z‖ₑ ^ p.toReal := by
      exact (lintegral_prod_symm _ (hF.continuous.enorm.measurable.pow_const _).aemeasurable).symm
    _ ≤ _ := by
      have hb := flatLift_lintegral_rpow_le (deriv standardCutoff) (standardMollifier n) (representative u)
        hχd (standardMollifier_contDiff n) (standardMollifier_compactSupport n) (representative_contDiff u)
        p Fact.out hp hfp
      rw [hmass, standardMollifier_eLpNorm_one, one_mul, hrepnorm] at hb
      apply hb.trans
      apply mul_le_mul' le_rfl
      apply ENNReal.rpow_le_rpow _ hpr.le
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (norm_le_fractionalNorm s p u.val)

/-- Power integrals of a sum require measurability of only one summand. -/
lemma flat_lintegral_sum_rpow_le {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (A B : Domain n × ℝ → 𝕜) (q : ℝ) (hq : 1 ≤ q)
    (hB : Measurable (fun z => ‖B z‖ₑ ^ q)) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ y : Domain n, ‖A (y, t) + B (y, t)‖ₑ ^ q) ≤
      (2 : ℝ≥0∞) ^ (q - 1) *
        ((∫⁻ t in Ioi (0 : ℝ), ∫⁻ y : Domain n, ‖A (y, t)‖ₑ ^ q) +
          ∫⁻ t in Ioi (0 : ℝ), ∫⁻ y : Domain n, ‖B (y, t)‖ₑ ^ q) := by
  have hfin : (2 : ℝ≥0∞) ^ (q - 1) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), ∫⁻ y : Domain n,
        (2 : ℝ≥0∞) ^ (q - 1) * (‖A (y, t)‖ₑ ^ q + ‖B (y, t)‖ₑ ^ q) := by
      apply lintegral_mono
      intro t
      apply lintegral_mono
      intro y
      exact (ENNReal.rpow_le_rpow (enorm_add_le _ _) (by linarith)).trans
        (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hq)
    _ = ∫⁻ t in Ioi (0 : ℝ), (2 : ℝ≥0∞) ^ (q - 1) *
        ((∫⁻ y : Domain n, ‖A (y, t)‖ₑ ^ q) + ∫⁻ y : Domain n, ‖B (y, t)‖ₑ ^ q) := by
      apply lintegral_congr
      intro t
      have hBt : Measurable (fun y : Domain n => ‖B (y, t)‖ₑ ^ q) := hB.comp measurable_prodMk_right
      rw [lintegral_const_mul' _ _ hfin, lintegral_add_right _ hBt]
    _ = _ := by
      rw [lintegral_const_mul' _ _ hfin,
        lintegral_add_right _ hB.lintegral_prod_left']

lemma canonical_cutoff_power_ne_top (p : ℝ≥0∞) :
    eLpNorm (deriv standardCutoff) p volume ^ p.toReal ≠ ∞ := by
  have hχd : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv standardCutoff) := by
    exact (standardCutoff_contDiff.fderiv_right (by simp)).clm_apply contDiff_const
  have hmem : MemLp (deriv standardCutoff) p volume :=
    hχd.continuous.memLp_of_hasCompactSupport standardCutoff_compactSupport.deriv
  exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hmem.eLpNorm_ne_top


open KernelEstimates

lemma standardCutoff_norm_le_one (t : ℝ) : ‖standardCutoff t‖ ≤ 1 := by
  change ‖(⟨1, 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ)) t‖ ≤ 1
  rw [Real.norm_of_nonneg (ContDiffBump.nonneg _)]
  exact ContDiffBump.le_one _

lemma standardCutoff_enorm_le_one (t : ℝ) : ‖standardCutoff t‖ₑ ≤ 1 := by
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_one.mpr (standardCutoff_norm_le_one t)

def canonicalDerivativeKernel (n : ℕ) : Option (Fin n) → Domain n → ℝ
  | none => normalKernel (standardMollifier n)
  | some j => fun y => fderiv ℝ (standardMollifier n) y (coordinateVector j)

lemma canonicalDerivativeKernel_continuous (n : ℕ) (j : Option (Fin n)) :
    Continuous (canonicalDerivativeKernel n j) := by
  cases j with
  | none => exact normalKernel_continuous _ ((standardMollifier_contDiff n).of_le (by simp))
  | some j => exact ((standardMollifier_contDiff n).continuous_fderiv (by simp)).clm_apply continuous_const

lemma canonicalDerivativeKernel_compactSupport (n : ℕ) (j : Option (Fin n)) :
    HasCompactSupport (canonicalDerivativeKernel n j) := by
  cases j with
  | none => exact normalKernel_hasCompactSupport _ (standardMollifier_compactSupport n)
  | some j => exact (standardMollifier_compactSupport n).fderiv_apply ℝ (coordinateVector j)

lemma canonicalDerivativeKernel_integral_zero (n : ℕ) (j : Option (Fin n)) :
    ∫ y, canonicalDerivativeKernel n j y = 0 := by
  cases j with
  | none =>
      exact normalKernel_integral _ ((standardMollifier_contDiff n).of_le (by simp))
        (standardMollifier_compactSupport n)
  | some j =>
      exact kernel_directional_integral_zero _ (standardMollifier_compactSupport n)
        ((standardMollifier_contDiff n).of_le (by simp)) (coordinateVector j)


lemma cutoff_kernel_energy_le {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (K : Domain n → ℝ) (f : Domain n → 𝕜) (D : Domain n × ℝ → 𝕜)
    (hD : ∀ x t, 0 < t → D (x,t) = standardCutoff t •
      convolution (derivativeScaledKernel K t) f (ContinuousLinearMap.lsmul ℝ ℝ) volume x) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖D (x,t)‖ₑ ^ p.toReal) ≤
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖∫ h, derivativeScaledKernel K t h • f (x-h)‖ₑ ^ p.toReal := by
  have hpr : 0 ≤ p.toReal := ENNReal.toReal_nonneg
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  apply lintegral_mono
  intro x
  dsimp only
  rw [hD x t ht]
  apply ENNReal.rpow_le_rpow _ hpr
  calc
    ‖standardCutoff t • convolution (derivativeScaledKernel K t) f
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ =
      ‖standardCutoff t‖ₑ * ‖convolution (derivativeScaledKernel K t) f
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ := enorm_smul _ _
    _ ≤ 1 * ‖convolution (derivativeScaledKernel K t) f
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ := mul_le_mul' (standardCutoff_enorm_le_one t) le_rfl
    _ = _ := by rw [one_mul]; rfl


lemma canonical_partial_bounds_of_cutoff_bound
    (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞)
    (A : ℝ≥0∞) (hA : A ≠ ∞)
    (hcut : ∀ (𝕜 : Type) [RCLike 𝕜]
      (u : Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothData 𝕜 n (1 - 1 / p.toReal) p),
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ y : Domain n,
        ‖deriv standardCutoff t • average (standardMollifier n) (representative u) (y,t)‖ₑ ^ p.toReal) ≤
        A * ENNReal.ofReal (fractionalNorm (1 - 1 / p.toReal) p u.val) ^ p.toReal) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (𝕜 : Type) [RCLike 𝕜] (i : Fin (n + 1))
      (u : Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothData 𝕜 n (1 - 1 / p.toReal) p)
      (j : Fin (n + 1)),
      ‖(canonicalLift i u).val (ExpandedFA.Sobolev.HalfSpace.coordinateIndex j)‖ ≤
        L * fractionalNorm (1 - 1 / p.toReal) p u.val := by
  have hq : 1 < p.toReal := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).mpr hp1
  have hK := fun j : Option (Fin n) => derivativeScaledKernel_energy_bound p hp1 hp
    (canonicalDerivativeKernel n j) (canonicalDerivativeKernel_continuous n j)
    (canonicalDerivativeKernel_compactSupport n j) (canonicalDerivativeKernel_integral_zero n j)
  choose C hC hCE using hK
  let S : ℝ≥0∞ := ∑ j : Option (Fin n), C j
  let T : ℝ≥0∞ := 2 ^ (p.toReal - 1)
  let B : ℝ≥0∞ := T * (S + A)
  have hS : S ≠ ∞ := by
    dsimp only [S]
    exact (ENNReal.sum_lt_top.mpr fun j _ => lt_top_iff_ne_top.mpr (hC j)).ne
  have hT : T ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
  have hT1 : 1 ≤ T := ENNReal.one_le_rpow (by norm_num) (by linarith)
  have hB : B ≠ ∞ := ENNReal.mul_ne_top hT (ENNReal.add_ne_top.mpr ⟨hS,hA⟩)
  have hCS : ∀ j, C j ≤ S := fun j =>
    Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ j)
  have hSB : S ≤ B := by
    calc
      S ≤ S + A := le_add_right le_rfl
      _ = 1 * (S + A) := (one_mul _).symm
      _ ≤ B := mul_le_mul' hT1 le_rfl
  refine ⟨B.toReal ^ (1 / p.toReal), Real.rpow_nonneg ENNReal.toReal_nonneg _, ?_⟩
  intro 𝕜 _ i u j
  let f := representative u
  let ρ := standardMollifier n
  have hf := representative_contDiff u
  have hfc := representative_compactSupport u
  have hρ := standardMollifier_contDiff n
  have hρc := standardMollifier_compactSupport n
  have hF := flatLift_contDiff standardCutoff ρ f standardCutoff_contDiff hρ hρc hf
  have hFA := average_contDiff ρ f hρ hρc hf
  let N := fractionalNorm (1 - 1 / p.toReal) p u.val
  let P := ENNReal.ofReal N ^ p.toReal
  have hN : 0 ≤ N := fractionalNorm_nonneg _ _ _
  have henergy : differenceEnergy (1 - 1 / p.toReal) p u.val.val ≤ P :=
    differenceEnergy_le_fractionalNorm_rpow _ p hp u.val
  have hkernel (k : Option (Fin n)) (D : Domain n × ℝ → 𝕜)
      (hD : ∀ x t, 0 < t → D (x,t) = standardCutoff t •
        convolution (derivativeScaledKernel (canonicalDerivativeKernel n k) t) f
          (ContinuousLinearMap.lsmul ℝ ℝ) volume x) :
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ y : Domain n, ‖D (y,t)‖ₑ ^ p.toReal) ≤ C k * P := by
    exact ((cutoff_kernel_energy_le p hp _ f D hD).trans
      (hCE k 𝕜 u.val.val f hf.continuous (representative_ae u))).trans
      (mul_le_mul' le_rfl henergy)
  rcases Fin.eq_self_or_eq_succAbove i j with hji | ⟨k,hjk⟩
  · subst j
    let D : Domain n × ℝ → 𝕜 := fun z => fderiv ℝ (flatLift standardCutoff ρ f) z (0,1)
    let D₁ : Domain n × ℝ → 𝕜 := fun z => standardCutoff z.2 • fderiv ℝ (average ρ f) z (0,1)
    let D₂ : Domain n × ℝ → 𝕜 := fun z => deriv standardCutoff z.2 • average ρ f z
    have hDmeas : Measurable (fun z => ‖D z‖ₑ ^ p.toReal) :=
      ((hF.continuous_fderiv (by simp)).clm_apply continuous_const).enorm.measurable.pow_const _
    have hD₂meas : Measurable (fun z => ‖D₂ z‖ₑ ^ p.toReal) := by
      have hdχ : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv standardCutoff) :=
        (standardCutoff_contDiff.fderiv_right (by simp)).clm_apply contDiff_const
      exact ((hdχ.continuous.comp continuous_snd).smul hFA.continuous).enorm.measurable.pow_const _
    have hsum : D = D₁ + D₂ := by
      funext z
      exact flatLift_fderiv_normal standardCutoff ρ f standardCutoff_contDiff hρ hρc hf z
    have hD₁ : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ y : Domain n, ‖D₁ (y,t)‖ₑ ^ p.toReal) ≤ C none * P := by
      apply hkernel none D₁
      intro x t ht
      dsimp only [D₁]
      rw [average_fderiv_normal ρ f hρ hρc hf]
      rw [average_deriv_normal_formula ρ f (hρ.of_le (by simp)) hρc (hf.of_le (by simp)) hfc x ht]
      rfl
    have hbound : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ y : Domain n, ‖D (y,t)‖ₑ ^ p.toReal) ≤ B * P := by
      rw [hsum]
      calc
        _ ≤ T * ((∫⁻ t in Ioi (0 : ℝ), ∫⁻ y : Domain n, ‖D₁ (y,t)‖ₑ ^ p.toReal) +
          ∫⁻ t in Ioi (0 : ℝ), ∫⁻ y : Domain n, ‖D₂ (y,t)‖ₑ ^ p.toReal) :=
            flat_lintegral_sum_rpow_le D₁ D₂ p.toReal hq.le hD₂meas
        _ ≤ T * (C none * P + A * P) :=
          mul_le_mul' le_rfl (add_le_add hD₁ (hcut 𝕜 u))
        _ = T * ((C none + A) * P) := by rw [add_mul]
        _ ≤ T * ((S + A) * P) := by gcongr; exact hCS none
        _ = B * P := by dsimp only [B]; ring
    exact smoothDataLift_partial_norm_le_of_flat_bound i standardCutoff ρ standardCutoff_contDiff
      standardCutoff_compactSupport hρ hρc hp u i D hDmeas
      (fun x _ => by
        rw [liftFunction_fderiv_coordinates i standardCutoff ρ f standardCutoff_contDiff hρ hρc hf,
          flatCoordinatesCLM_normal]) B hB N hN hbound
  · subst j
    let D : Domain n × ℝ → 𝕜 := fun z =>
      fderiv ℝ (flatLift standardCutoff ρ f) z (coordinateVector k,0)
    have hDmeas : Measurable (fun z => ‖D z‖ₑ ^ p.toReal) :=
      ((hF.continuous_fderiv (by simp)).clm_apply continuous_const).enorm.measurable.pow_const _
    have hbound : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ y : Domain n, ‖D (y,t)‖ₑ ^ p.toReal) ≤ B * P := by
      apply (hkernel (some k) D ?_).trans (mul_le_mul' ((hCS _).trans hSB) le_rfl)
      intro x t ht
      rw [show D (x,t) = standardCutoff t • fderiv ℝ (average ρ f) (x,t) (coordinateVector k,0) from
        flatLift_fderiv_tangential standardCutoff ρ f standardCutoff_contDiff hρ hρc hf (x,t) (coordinateVector k)]
      rw [average_fderiv_spatial_kernel ρ f hρ hρc hf (x,t) ht]
      congr 1
      change (∫ y, ((t ^ n)⁻¹ * t⁻¹ * fderiv ℝ ρ (t⁻¹ • y) (coordinateVector k)) • f (x-y)) = _
      simp only [convolution, derivativeScaledKernel, canonicalDerivativeKernel, pow_succ, mul_inv_rev]
      congr 1
      funext y
      congr 1 <;> ring
    exact smoothDataLift_partial_norm_le_of_flat_bound i standardCutoff ρ standardCutoff_contDiff
      standardCutoff_compactSupport hρ hρc hp u (i.succAbove k) D hDmeas
      (fun x _ => by
        rw [liftFunction_fderiv_coordinates i standardCutoff ρ f standardCutoff_contDiff hρ hρc hf,
          flatCoordinatesCLM_tangential]) B hB N hN hbound


/-- Uniform bounds for every actual first derivative of the canonical lift.
The fixed real kernels make the constant depend only on n and p. -/
theorem canonical_partial_bounds :
    ∀ (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
      ∃ L : ℝ, 0 ≤ L ∧ ∀ (𝕜 : Type) [RCLike 𝕜] (i : Fin (n + 1))
        (u : Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothData 𝕜 n (1 - 1 / p.toReal) p)
        (j : Fin (n + 1)),
        ‖(canonicalLift i u).val (ExpandedFA.Sobolev.HalfSpace.coordinateIndex j)‖ ≤
          L * fractionalNorm (1 - 1 / p.toReal) p u.val := by
  intro n p _ hp1 hp
  exact canonical_partial_bounds_of_cutoff_bound n p hp1 hp
    (eLpNorm (deriv standardCutoff) p volume ^ p.toReal) (canonical_cutoff_power_ne_top p)
    (fun 𝕜 _ u => canonical_cutoff_flat_power_bound p hp u)


end SmoothLift

section Assembly
open ExpandedFA.Sobolev ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open Specs.ExpandedFA.PartIV.SharpTraceExtension
open ExpandedFA.PartIV.SharpTraceBound

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (s : ℝ) (p : ℝ≥0∞)
  [Fact (1 ≤ p)] [Fact (p ≠ ∞)]

/-- Forgetting fractional increments is bounded by the full norm. -/
def fractionalInclusion : FractionalSpace 𝕜 n s p →L[𝕜]
    Lp 𝕜 p (volume : Measure (Domain n)) :=
  (show FractionalSpace 𝕜 n s p →ₗ[𝕜] Lp 𝕜 p volume from
    { toFun := Subtype.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).mkContinuous 1 (fun u => by
        change ‖u.val‖ ≤ 1 * fractionalNorm s p u
        simpa only [one_mul] using norm_le_fractionalNorm s p u)

@[simp] lemma fractionalError_eq_norm (u v : FractionalSpace 𝕜 n s p) :
    fractionalError s p u.val v.val = ‖u - v‖ := rfl

/-- The smooth finite-energy members form the subspace to which the explicit
kernel construction is first applied. -/
def smoothFractionalSubmodule : Submodule 𝕜 (FractionalSpace 𝕜 n s p) where
  carrier := {u | ∃ f : Domain n → 𝕜, ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧
    HasCompactSupport f ∧ u.val =ᵐ[volume] f}
  zero_mem' := ⟨0, contDiff_const, by simp [HasCompactSupport, tsupport], Lp.coeFn_zero 𝕜 p volume⟩
  add_mem' := by
    rintro u v ⟨f, hf, hfc, huf⟩ ⟨g, hg, hgc, hvg⟩
    refine ⟨f + g, hf.add hg, hfc.add hgc, ?_⟩
    filter_upwards [Lp.coeFn_add u.val v.val, huf, hvg] with x hx hu hv
    change (u.val + v.val) x = f x + g x
    simp only [Pi.add_apply] at hx
    rw [hx, hu, hv]
  smul_mem' := by
    rintro c u ⟨f, hf, hfc, huf⟩
    refine ⟨c • f, hf.const_smul c, ?_, ?_⟩
    · exact hfc.smul_left
    · filter_upwards [Lp.coeFn_smul c u.val, huf] with x hx hu
      change (c • u.val) x = c • f x
      simp only [Pi.smul_apply] at hx
      rw [hx, hu]

/-- The epsilon formulation of smooth density gives the required dense range
in the full fractional norm topology. -/
lemma smoothFractional_denseRange (hd : SmoothDensity) (hs0 : 0 < s) (hs1 : s < 1) :
    DenseRange (smoothFractionalSubmodule (𝕜 := 𝕜) (n := n) s p).subtype := by
  intro u
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨v, f, hf, hfc, hv, herr⟩ := hd 𝕜 n s hs0 hs1 p Fact.out u ε hε
  refine ⟨v, ⟨⟨v, f, hf, hfc, hv⟩, rfl⟩, ?_⟩
  rw [dist_comm, dist_eq_norm, ← fractionalError_eq_norm]
  exact herr

/-- Density and the smooth construction suffice; no surjectivity or splitting
of an arbitrary Banach quotient is invoked. -/
theorem bounded_right_inverse_of_smooth_density :
    Specs.ExpandedFA.PartIV.SharpTraceExtension.Assembly := by
  intro hd hl n p _ hp1 hp
  letI : Fact (p ≠ ∞) := ⟨hp⟩
  obtain ⟨C, hC, hE⟩ := hl n p hp1 hp
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _ i
  let s := 1 - 1 / p.toReal
  let S := smoothFractionalSubmodule (𝕜 := 𝕜) (n := n) s p
  have hs := endpoint_exponent hp1 hp
  have hS : DenseRange S.subtype := smoothFractional_denseRange s p hd hs.1 hs.2
  obtain ⟨E₀, hAdd, hSmul, hBound, hTrace⟩ := hE 𝕜 i
  let L : S →ₗ[𝕜] SpaceValue 𝕜 (n + 1) (upper i) 1 p :=
    { toFun := E₀
      map_add' := fun u v => hAdd u v (u + v) rfl
      map_smul' := fun c u => hSmul c u (c • u) rfl }
  letI : CompleteSpace (SpaceValue 𝕜 (n + 1) (upper i) 1 p) :=
    ExpandedFA.Sobolev.sobolev_complete 𝕜 (n + 1) (upper i) 1 p
  let E := L.extendOfNorm S.subtype
  have hL : ∀ u, ‖L u‖ ≤ C * ‖S.subtype u‖ := hBound
  have hAgree : ∀ u : S, E (S.subtype u) = E₀ u :=
    fun u => L.extendOfNorm_eq hS ⟨C, hL⟩ u
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · intro u v w hw
    have hw' : w = u + v := Subtype.ext hw
    rw [hw', map_add]
  · intro c u v hv
    have hv' : v = c • u := Subtype.ext hv
    rw [hv', map_smul]
  · exact L.norm_extendOfNorm_apply_le hS C hL
  · intro T hT
    have heq : (fun u => reindexedTrace i T (E u)) = fractionalInclusion s p := by
      apply hS.equalizer ((reindexedTrace i T).continuous.comp E.continuous)
        (fractionalInclusion s p).continuous
      funext u
      change reindexedTrace i T (E (S.subtype u)) = u.val.val
      rw [hAgree u]
      exact hTrace T hT u
    intro u
    exact congrFun heq u

end Assembly

/-- The explicit smooth lift has the full dimension/p-uniform Sobolev bound. -/
theorem smooth_right_inverse :
    Specs.ExpandedFA.PartIV.SharpTraceExtension.SmoothRightInverse :=
  SmoothLift.smooth_right_inverse_of_canonical_partial_bounds SmoothLift.canonical_partial_bounds

/-- The sharp half-space trace admits a bounded scalar-linear right inverse
on every finite-energy datum, with the full first-derivative norm estimate. -/
theorem bounded_right_inverse :
    Specs.ExpandedFA.PartIV.SharpTraceExtension.BoundedRightInverse :=
  bounded_right_inverse_of_smooth_density smooth_density smooth_right_inverse

end ExpandedFA.PartIV.SharpTraceExtension
