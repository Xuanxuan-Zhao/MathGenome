import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.HardyAveragingLp
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.CompactNonzeroSpectrum
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.Conventions
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Module
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.HardyAveragingContinuous
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.HardyAveragingRealBridge

import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Operator.Extend

noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology

namespace ExpandedFA.PartV.HardyAveragingLp

open Spec

lemma toReal_gt_one {p : ℝ≥0∞} (hp : 1 < p) (hpfin : p ≠ ∞) : 1 < p.toReal := by
  exact_mod_cast (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hpfin).mpr hp

lemma threshold_pos {p : ℝ≥0∞} (hp : 1 < p) (hpfin : p ≠ ∞) : 0 < threshold p := by
  have h := toReal_gt_one hp hpfin
  dsimp [threshold]
  exact sub_pos.mpr ((div_lt_one (by linarith : 0 < p.toReal)).mpr h)

/-- Exact power integrability, without imposing any regularity at zero. -/
lemma memLp_cpow_iff {p : ℝ≥0∞} (hp : 0 < p) (hpfin : p ≠ ∞) (b : ℂ) :
    MemLp (fun x : ℝ => (x : ℂ) ^ b) p intervalMeasure ↔ -1 < b.re * p.toReal := by
  have hm : AEStronglyMeasurable (fun x : ℝ => (x : ℂ) ^ b) intervalMeasure := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioo
    apply continuousOn_of_forall_continuousAt
    intro x hx
    exact Complex.continuousAt_ofReal_cpow_const x b (Or.inr hx.1.ne')
  rw [← integrable_norm_rpow_iff hm hp.ne' hpfin]
  have heq : (fun x : ℝ => ‖(x : ℂ) ^ b‖ ^ p.toReal) =ᵐ[intervalMeasure]
      (fun x : ℝ => x ^ (b.re * p.toReal)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx.1, ← Real.rpow_mul hx.1.le]
  rw [integrable_congr heq]
  exact intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one

theorem power_membership {p : ℝ≥0∞} (hp : 1 < p) (hpfin : p ≠ ∞) :
    Spec.PowerMembership p := by
  intro z hz
  change MemLp (fun x : ℝ => (x : ℂ) ^ (z⁻¹ - 1)) p intervalMeasure ↔ _
  rw [memLp_cpow_iff (lt_trans (by norm_num) hp) hpfin]
  have hpos : 0 < p.toReal := lt_trans zero_lt_one (toReal_gt_one hp hpfin)
  simp only [Complex.sub_re, Complex.one_re]
  dsimp [threshold]
  simp only [one_div]
  constructor
  · intro h
    have hdiv : -1 / p.toReal < (z⁻¹).re - 1 := (div_lt_iff₀ hpos).mpr h
    simp only [neg_div, one_div] at hdiv
    linarith
  · intro h
    apply (div_lt_iff₀ hpos).mp
    simp only [neg_div, one_div]
    linarith

lemma conjugateExponent_pos {p : ℝ≥0∞} (hp : 1 < p) (hpfin : p ≠ ∞) :
    0 < conjugateExponent p := inv_pos.mpr (threshold_pos hp hpfin)

lemma conjugateExponent_eq_div {p : ℝ≥0∞} (hp : 1 < p) (hpfin : p ≠ ∞) :
    conjugateExponent p = p.toReal / (p.toReal - 1) := by
  have ht := toReal_gt_one hp hpfin
  dsimp [conjugateExponent, threshold]
  field_simp

/-- The disk has diameter [0, 1/c], including the singular point zero
only on its boundary. -/
lemma inverse_re_gt_iff_disk (c : ℝ) (hc : 0 < c) (z : ℂ) (hz : z ≠ 0) :
    c < (z⁻¹).re ↔ ‖z - ((c⁻¹ / 2 : ℝ) : ℂ)‖ < c⁻¹ / 2 := by
  have hs : ‖z - ((c⁻¹ / 2 : ℝ) : ℂ)‖ ^ 2 =
      Complex.normSq z - c⁻¹ * z.re + (c⁻¹ / 2) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    ring
  have hi : 0 < c⁻¹ := inv_pos.mpr hc
  rw [Complex.inv_re, lt_div_iff₀ (Complex.normSq_pos.mpr hz)]
  constructor
  · intro h
    have hm := mul_lt_mul_of_pos_left h hi
    simp only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at hm
    apply (sq_lt_sq₀ (norm_nonneg _) (by positivity : 0 ≤ c⁻¹ / 2)).mp
    nlinarith
  · intro h
    have hh := (sq_lt_sq₀ (norm_nonneg _) (by positivity : 0 ≤ c⁻¹ / 2)).mpr h
    have hlt : Complex.normSq z < c⁻¹ * z.re := by nlinarith
    have hm := mul_lt_mul_of_pos_left hlt hc
    simpa only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] using hm

lemma inverse_re_lt_iff_exterior (c : ℝ) (hc : 0 < c) (z : ℂ) (hz : z ≠ 0) :
    (z⁻¹).re < c ↔ c⁻¹ / 2 < ‖z - ((c⁻¹ / 2 : ℝ) : ℂ)‖ := by
  have hs : ‖z - ((c⁻¹ / 2 : ℝ) : ℂ)‖ ^ 2 =
      Complex.normSq z - c⁻¹ * z.re + (c⁻¹ / 2) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    ring
  have hi : 0 < c⁻¹ := inv_pos.mpr hc
  rw [Complex.inv_re, div_lt_iff₀ (Complex.normSq_pos.mpr hz)]
  constructor
  · intro h
    have hm := mul_lt_mul_of_pos_left h hi
    simp only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at hm
    apply (sq_lt_sq₀ (by positivity : 0 ≤ c⁻¹ / 2) (norm_nonneg _)).mp
    nlinarith
  · intro h
    have hh := (sq_lt_sq₀ (by positivity : 0 ≤ c⁻¹ / 2) (norm_nonneg _)).mpr h
    have hlt : c⁻¹ * z.re < Complex.normSq z := by nlinarith
    have hm := mul_lt_mul_of_pos_left hlt hc
    simpa only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] using hm

/-- The canonical finite conjugate exponent, with its exact real value. -/
lemma conjugate_exponent_data {p : ℝ≥0∞} (hp : 1 < p) (_hpfin : p ≠ ∞) :
    let q : ℝ≥0∞ := (1 - p⁻¹)⁻¹
    ENNReal.HolderConjugate p q ∧ 0 < q ∧ q ≠ ∞ ∧
      q.toReal = conjugateExponent p := by
  dsimp only
  have hi : p⁻¹ < 1 := ENNReal.inv_lt_one.mpr hp
  have hq : ENNReal.HolderConjugate p ((1 - p⁻¹)⁻¹) := by
    constructor
    simp only [inv_inv, inv_one]
    exact add_tsub_cancel_of_le hi.le
  refine ⟨hq, ENNReal.inv_pos.mpr ?_, ?_, ?_⟩
  · exact ne_of_lt ((tsub_le_self : (1 : ℝ≥0∞) - p⁻¹ ≤ 1).trans_lt (by simp))
  · exact ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr hi).ne'
  · rw [ENNReal.toReal_inv, ENNReal.toReal_sub_of_le hi.le ENNReal.one_ne_top,
      ENNReal.toReal_one, ENNReal.toReal_inv]
    simp only [conjugateExponent, threshold, one_div]

/-- Hölder proves convergence of the weighted primitive at zero for every Lp
class, before any bounded weighted averaging operator has been constructed. -/
theorem weighted_primitive_integrable {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hpfin : p ≠ ∞) (a : ℂ) (ha : a.re < threshold p)
    (f : Space p) :
    ∀ x ∈ Ioc (0 : ℝ) 1,
      IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-a) * f t) volume 0 x := by
  let q : ℝ≥0∞ := (1 - p⁻¹)⁻¹
  obtain ⟨hq, hqpos, hqfin, hqreal⟩ := conjugate_exponent_data hp hpfin
  have : ENNReal.HolderConjugate p q := hq
  have hweight : MemLp (fun t : ℝ => (t : ℂ) ^ (-a)) q intervalMeasure := by
    rw [memLp_cpow_iff hqpos hqfin, Complex.neg_re, hqreal]
    have hc := threshold_pos hp hpfin
    have hh := mul_lt_mul_of_pos_right ha (inv_pos.mpr hc)
    rw [mul_inv_cancel₀ hc.ne'] at hh
    dsimp [conjugateExponent]
    linarith
  have hint : Integrable (fun t : ℝ => (t : ℂ) ^ (-a) * f t) intervalMeasure :=
    hweight.integrable_mul (Lp.memLp f)
  intro x hx
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hx.1.le).mpr
  change IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-a) * f t) (Ioo 0 1) volume at hint
  exact hint.mono_set (Ioo_subset_Ioo_right hx.2)

/-- Every weighted primitive evaluation is continuous in the Lp norm, by the
scalar-linear Hölder pairing with a truncated power weight. -/
lemma weightedAverage_continuous {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hpfin : p ≠ ∞) (a : ℂ) (ha : a.re < threshold p)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Continuous (fun f : Space p => weightedAverage a (f : ℝ → ℂ) x) := by
  let q : ℝ≥0∞ := (1 - p⁻¹)⁻¹
  obtain ⟨hq, hqpos, hqfin, hqreal⟩ := conjugate_exponent_data hp hpfin
  have : ENNReal.HolderConjugate p q := hq
  have : Fact (1 ≤ q) := ⟨hq.symm.one_le⟩
  have hweight : MemLp (fun t : ℝ => (t : ℂ) ^ (-a)) q intervalMeasure := by
    rw [memLp_cpow_iff hqpos hqfin, Complex.neg_re, hqreal]
    have hc := threshold_pos hp hpfin
    have hh := mul_lt_mul_of_pos_right ha (inv_pos.mpr hc)
    rw [mul_inv_cancel₀ hc.ne'] at hh
    dsimp [conjugateExponent]
    linarith
  let w : ℝ → ℂ := (Ioo (0 : ℝ) x).indicator (fun t : ℝ => (t : ℂ) ^ (-a))
  have hw : MemLp w q intervalMeasure := hweight.indicator measurableSet_Ioo.nullMeasurableSet
  let W : Lp ℂ q intervalMeasure := hw.toLp w
  let B : Space p →L[ℂ] ℂ :=
    ((ContinuousLinearMap.mul ℂ ℂ).lpPairing intervalMeasure q p) W
  have hB (f : Space p) : B f = ∫ t in (0 : ℝ)..x, (t : ℂ) ^ (-a) * f t := by
    dsimp [B]
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    calc
      (∫ t, W t * f t ∂intervalMeasure) = ∫ t, w t * f t ∂intervalMeasure := by
        apply integral_congr_ae
        filter_upwards [hw.coeFn_toLp] with t ht
        rw [ht]
      _ = ∫ t in Ioo (0 : ℝ) x, (t : ℂ) ^ (-a) * f t ∂intervalMeasure := by
        rw [← integral_indicator measurableSet_Ioo]
        apply integral_congr_ae
        filter_upwards [] with t
        by_cases ht : t ∈ Ioo (0 : ℝ) x <;> simp [w, ht]
      _ = ∫ t in (0 : ℝ)..x, (t : ℂ) ^ (-a) * f t := by
        change (∫ t in Ioo (0 : ℝ) x, (t : ℂ) ^ (-a) * f t
          ∂(volume.restrict (Ioo (0 : ℝ) 1))) = _
        rw [Measure.restrict_restrict measurableSet_Ioo,
          inter_eq_left.mpr (Ioo_subset_Ioo_right hx.2.le),
          intervalIntegral.integral_of_le hx.1.le, integral_Ioc_eq_integral_Ioo]
  have heq : (fun f : Space p => weightedAverage a (f : ℝ → ℂ) x) =
      (fun f => (x : ℂ) ^ (a - 1) * B f) := by
    funext f
    rw [hB]
    rfl
  rw [heq]
  exact continuous_const.mul B.continuous

/-- A Hardy primitive is continuous even when its Lp density is only measurable. -/
lemma primitive_continuousOn {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (Q : Space p →L[ℂ] Space p) (hQ : IsHardy Q) (f : Space p) :
    ContinuousOn (fun x => ∫ t in (0 : ℝ)..x, f t) (Icc (0 : ℝ) 1) := by
  simpa only [uIcc_of_le zero_le_one] using
    intervalIntegral.continuousOn_primitive_interval' ((hQ f).1 1 ⟨zero_lt_one, le_rfl⟩)
      (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 1)

/-- Vanishing of the averaging class forces vanishing of the density class.
This uses the a.e. FTC, without differentiating an arbitrary representative. -/
theorem hardy_injective {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (Q : Space p →L[ℂ] Space p) (hQ : IsHardy Q) : NoZeroEigenvalue Q := by
  apply (injective_iff_map_eq_zero Q).mpr
  intro f hf
  have hav : Spec.average (f : ℝ → ℂ) =ᵐ[intervalMeasure] 0 := by
    have hzero : (Q f : ℝ → ℂ) =ᵐ[intervalMeasure] 0 := by
      rw [hf]
      exact Lp.coeFn_zero _ _ _
    exact (hQ f).2.symm.trans hzero
  have hprim : (fun x => ∫ t in (0 : ℝ)..x, f t) =ᵐ[intervalMeasure] 0 := by
    filter_upwards [hav, ae_restrict_mem measurableSet_Ioo] with x hx hmem
    dsimp [Spec.average] at hx
    exact (mul_eq_zero.mp hx).resolve_left (inv_ne_zero (Complex.ofReal_ne_zero.mpr hmem.1.ne'))
  have heq : EqOn (fun x => ∫ t in (0 : ℝ)..x, f t) (fun _ => (0 : ℂ))
      (Ioo (0 : ℝ) 1) :=
    Measure.eqOn_Ioo_of_ae_eq volume hprim
      ((primitive_continuousOn Q hQ f).mono Ioo_subset_Icc_self) continuousOn_const
  have hder := ((hQ f).1 1 ⟨zero_lt_one, le_rfl⟩).ae_hasDerivAt_integral
  apply Lp.ext
  refine (Filter.EventuallyEq.trans ?_ (Lp.coeFn_zero ℂ p intervalMeasure).symm)
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [hder] with x hx hmem
  have hd := hx (by simpa using Ioo_subset_Icc_self hmem) 0 left_mem_uIcc
  have hz : HasDerivAt (fun y => ∫ t in (0 : ℝ)..y, f t) 0 x :=
    (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq
      (Filter.eventually_of_mem (Ioo_mem_nhds hmem.1 hmem.2) fun y hy => heq hy)
  exact hd.unique hz

/-- Local FTC for a density that agrees a.e. with a continuous function. -/
lemma primitive_hasDerivAt_of_ae_eq {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (Q : Space p →L[ℂ] Space p) (hQ : IsHardy Q) (f : Space p)
    (g : ℝ → ℂ) (hfg : (f : ℝ → ℂ) =ᵐ[intervalMeasure] g)
    (hg : ContinuousOn g (Ioo (0 : ℝ) 1)) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y => ∫ t in (0 : ℝ)..y, f t) (g x) x := by
  apply intervalIntegral.integral_hasDerivAt_of_tendsto_ae_right
    ((hQ f).1 x ⟨hx.1, hx.2.le⟩)
    (Lp.stronglyMeasurable f).stronglyMeasurableAtFilter
  have heq : (f : ℝ → ℂ) =ᶠ[𝓝 x ⊓ MeasureTheory.ae volume] g := by
    have ha := (ae_restrict_iff' measurableSet_Ioo).mp hfg
    filter_upwards [ha.filter_mono inf_le_right,
      (Filter.Eventually.filter_mono inf_le_left (Ioo_mem_nhds hx.1 hx.2))] with y hy hym
    exact hy hym
  exact ((hg.continuousAt (isOpen_Ioo.mem_nhds hx)).tendsto.mono_left inf_le_left).congr'
    heq.symm

/-- The measurable eigenvalue equation has a continuous representative locally
away from zero. Solving the resulting Euler equation classifies its density. -/
lemma eigenfunction_profile {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (Q : Space p →L[ℂ] Space p) (hQ : IsHardy Q)
    {z : ℂ} (hz : z ≠ 0) (f : Space p) (he : Q f = z • f) :
    ∃ c : ℂ, (f : ℝ → ℂ) =ᵐ[intervalMeasure] fun x => c * powerProfile z x := by
  let F : ℝ → ℂ := fun x => ∫ t in (0 : ℝ)..x, f t
  let a : ℂ := z⁻¹
  let g : ℝ → ℂ := fun x => a * ((x : ℂ)⁻¹ * F x)
  have ha : a ≠ 0 := inv_ne_zero hz
  have hfg : (f : ℝ → ℂ) =ᵐ[intervalMeasure] g := by
    have h := (hQ f).2
    rw [he] at h
    filter_upwards [h, Lp.coeFn_smul z f] with x hx hs
    simp only [Pi.smul_apply, smul_eq_mul] at hs
    dsimp [g, a, F]
    change f x = z⁻¹ * Spec.average (f : ℝ → ℂ) x
    rw [← hx, hs]
    simp [hz]
  have hg : ContinuousOn g (Ioo (0 : ℝ) 1) := by
    apply continuousOn_const.mul
    apply ContinuousOn.mul _ ((primitive_continuousOn Q hQ f).mono Ioo_subset_Icc_self)
    exact Complex.continuous_ofReal.continuousOn.inv₀
      (fun x hx => Complex.ofReal_ne_zero.mpr hx.1.ne')
  have hF (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt F (g x) x :=
    primitive_hasDerivAt_of_ae_eq Q hQ f g hfg hg hx
  let G : ℝ → ℂ := fun x => (x : ℂ) ^ (-a) * F x
  have hG (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt G 0 x := by
    have hd := (hasDerivAt_ofReal_cpow_const hx.1.ne' (neg_ne_zero.mpr ha)).mul (hF x hx)
    convert hd using 1
    dsimp [g]
    rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hx.1.ne'), Complex.cpow_one]
    ring
  obtain ⟨k, hk⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    (convex_Ioo (0 : ℝ) 1).isPreconnected
    (fun x hx => (hG x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hG x hx).deriv)
  refine ⟨a * k, ?_⟩
  filter_upwards [hfg, ae_restrict_mem measurableSet_Ioo] with x hx hxm
  have hx0 := Complex.ofReal_ne_zero.mpr hxm.1.ne'
  have hFval : F x = (x : ℂ) ^ a * k := by
    have hh := congrArg (fun w : ℂ => (x : ℂ) ^ a * w) (hk x hxm)
    dsimp [G] at hh
    rw [← mul_assoc, ← Complex.cpow_add _ _ hx0, add_neg_cancel, Complex.cpow_zero,
      one_mul] at hh
    exact hh
  rw [hx]
  dsimp [g, powerProfile]
  rw [hFval, Complex.cpow_sub _ _ hx0, Complex.cpow_one]
  dsimp [a]
  ring

lemma powerProfile_average {z : ℂ} (hz : z ≠ 0) (hpos : 0 < (z⁻¹).re)
    {x : ℝ} (hx : 0 < x) :
    Spec.average (powerProfile z) x = z * powerProfile z x := by
  have ha : z⁻¹ ≠ 0 := inv_ne_zero hz
  have hi := integral_cpow (a := (0 : ℝ)) (b := x) (r := z⁻¹ - 1)
    (Or.inl (by simpa using sub_lt_sub_right hpos 1))
  simp only [sub_add_cancel, Complex.ofReal_zero, Complex.zero_cpow ha, sub_zero] at hi
  dsimp [Spec.average, powerProfile]
  rw [hi, Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.cpow_one]
  simp only [div_eq_mul_inv, inv_inv]
  ring

/-- The converse eigenvalue equation is established by the actual integral,
using a.e. congruence of densities on every smaller interval. -/
lemma eigenfunction_of_profile {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hpfin : p ≠ ∞)
    (Q : Space p →L[ℂ] Space p) (hQ : IsHardy Q)
    {z : ℂ} (hz : z ≠ 0) (hmem : threshold p < (z⁻¹).re)
    (f : Space p) (c : ℂ)
    (hf : (f : ℝ → ℂ) =ᵐ[intervalMeasure] fun x => c * powerProfile z x) :
    Q f = z • f := by
  apply Lp.ext
  filter_upwards [(hQ f).2, hf, Lp.coeFn_smul z f,
    ae_restrict_mem measurableSet_Ioo] with x hx hfx hs hxm
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hs, hx, hfx]
  have hi : (∫ t in (0 : ℝ)..x, f t) = ∫ t in (0 : ℝ)..x, c * powerProfile z t := by
    apply intervalIntegral.integral_congr_ae'
    · filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp hf] with t ht htm
      exact ht ⟨htm.1, lt_of_le_of_lt htm.2 hxm.2⟩
    · filter_upwards [] with t ht
      exact False.elim ((not_lt_of_ge ht.2) (lt_trans hxm.1 ht.1))
  dsimp [Spec.average]
  rw [hi, intervalIntegral.integral_const_mul]
  have hav := powerProfile_average hz (lt_trans (threshold_pos hp hpfin) hmem) hxm.1
  dsimp [Spec.average] at hav
  calc
    _ = c * ((x : ℂ)⁻¹ * ∫ t in (0 : ℝ)..x, powerProfile z t) := by ring
    _ = _ := by rw [hav]; ring

lemma eigenfunction_coefficient_nonzero {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Space p) (hf : f ≠ 0) (z c : ℂ)
    (heq : (f : ℝ → ℂ) =ᵐ[intervalMeasure] fun x => c * powerProfile z x) : c ≠ 0 := by
  intro hc
  apply hf
  apply Lp.ext
  filter_upwards [heq, Lp.coeFn_zero ℂ p intervalMeasure] with x he hz
  rw [he, hc, zero_mul]
  exact hz.symm

theorem hardy_power_eigenfunctions {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hpfin : p ≠ ∞)
    (Q : Space p →L[ℂ] Space p) (hQ : IsHardy Q) : PowerEigenfunctions Q := by
  intro z hz f hf
  constructor
  · intro he
    obtain ⟨c, hc⟩ := eigenfunction_profile Q hQ hz f he
    have hc0 := eigenfunction_coefficient_nonzero f hf z c hc
    have hm : MemLp (powerProfile z) p intervalMeasure := by
      have hmul := ((memLp_congr_ae hc).mp (Lp.memLp f)).const_mul c⁻¹
      simpa only [← mul_assoc, inv_mul_cancel₀ hc0, one_mul] using hmul
    exact ⟨(power_membership hp hpfin z hz).mp hm, c, hc0, hc⟩
  · rintro ⟨hmem, c, _, hc⟩
    exact eigenfunction_of_profile hp hpfin Q hQ hz hmem f c hc

lemma powerProfile_not_ae_zero (z : ℂ) :
    ¬ (powerProfile z =ᵐ[intervalMeasure] (0 : ℝ → ℂ)) := by
  intro hzero
  have hfalse : ∀ᵐ x ∂intervalMeasure, False := by
    filter_upwards [hzero, ae_restrict_mem measurableSet_Ioo] with x hx hmem
    exact (Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr hmem.1.ne'))) hx
  have hmeasure := ae_iff.mp hfalse
  norm_num [intervalMeasure, Real.volume_Ioo] at hmeasure

theorem hardy_eigenvalue_disk {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hpfin : p ≠ ∞)
    (Q : Space p →L[ℂ] Space p) (hQ : IsHardy Q) : EigenvalueDisk Q := by
  apply Set.ext
  intro z
  constructor
  · rintro ⟨f, hf, he⟩
    have hz : z ≠ 0 := by
      intro hz
      have hzero : Q f = 0 := by simpa [hz] using he
      exact hf ((hardy_injective Q hQ) (hzero.trans (map_zero Q).symm))
    have hmem := ((hardy_power_eigenfunctions hp hpfin Q hQ z hz f hf).mp he).1
    exact (inverse_re_gt_iff_disk (threshold p) (threshold_pos hp hpfin) z hz).mp hmem
  · intro hmem
    have hz : z ≠ 0 := by
      intro hz
      have hd := half_pos (conjugateExponent_pos hp hpfin)
      simp only [hz, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hd, lt_self_iff_false, Set.mem_ofPred_eq] at hmem
    have hthr := (inverse_re_gt_iff_disk (threshold p) (threshold_pos hp hpfin) z hz).mpr hmem
    have hm := (power_membership hp hpfin z hz).mpr hthr
    let f : Space p := hm.toLp (powerProfile z)
    have hfeq : (f : ℝ → ℂ) =ᵐ[intervalMeasure] powerProfile z := hm.coeFn_toLp
    have hf : f ≠ 0 := by
      intro hf
      apply powerProfile_not_ae_zero z
      have hz' : (f : ℝ → ℂ) =ᵐ[intervalMeasure] 0 := by
        rw [hf]
        exact Lp.coeFn_zero ℂ p intervalMeasure
      exact hfeq.symm.trans hz'
    refine ⟨f, hf, eigenfunction_of_profile hp hpfin Q hQ hz hthr f 1 ?_⟩
    simpa only [one_mul] using hfeq

/-- The eigenfunction and no-zero-eigenvalue claims require only the stated
integral formula; they do not assume a spectral or boundedness certificate. -/
theorem eigenfunction_theorem : Spec.EigenfunctionTheorem := by
  intro p _ hp hpfin Q hQ
  exact ⟨hardy_injective Q hQ, hardy_power_eigenfunctions hp hpfin Q hQ,
    hardy_eigenvalue_disk hp hpfin Q hQ⟩

/-- Dilation shrinks the integration interval to (0,r); its pushforward
measure is bounded by r⁻¹ times Lebesgue measure on (0,1). -/
lemma dilation_map_measure_le {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Measure.map (fun x : ℝ => r * x) intervalMeasure ≤
      ENNReal.ofReal r⁻¹ • intervalMeasure := by
  have hpre : (fun x : ℝ => r * x) ⁻¹' Ioo 0 r = Ioo (0 : ℝ) 1 := by
    ext x
    change (0 < r * x ∧ r * x < r) ↔ 0 < x ∧ x < 1
    constructor
    · rintro ⟨h0, h1⟩
      constructor <;> nlinarith
    · rintro ⟨h0, h1⟩
      constructor <;> nlinarith
  have heq : Measure.map (fun x : ℝ => r * x) intervalMeasure =
      (Measure.map (fun x : ℝ => r * x) volume).restrict (Ioo 0 r) := by
    rw [Measure.restrict_map (by fun_prop) measurableSet_Ioo, hpre]
    rfl
  rw [heq, Real.map_volume_mul_left hr.ne', Measure.restrict_smul,
    abs_of_pos (inv_pos.mpr hr)]
  exact smul_le_smul_left _
    (Measure.restrict_mono_set volume (Ioo_subset_Ioo_right hr1))

/-- The dilation estimate at the level of the actual power-integral norm.
It applies to raw measurable representatives and includes arbitrary exponents. -/
lemma dilation_eLpNorm_le {p : ℝ≥0∞} (g : ℝ → ℂ) (hg : StronglyMeasurable g)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    eLpNorm (fun x : ℝ => g (r * x)) p intervalMeasure ≤
      ENNReal.ofReal r⁻¹ ^ (1 / p).toReal * eLpNorm g p intervalMeasure := by
  change eLpNorm (g ∘ (fun x : ℝ => r * x)) p intervalMeasure ≤ _
  rw [← eLpNorm_map_measure hg.aestronglyMeasurable (by fun_prop)]
  exact eLpNorm_le_of_measure_le_smul (dilation_map_measure_le hr hr1)

section ContinuousBridge

local instance : IsFiniteMeasure intervalMeasure := by
  dsimp [intervalMeasure]
  infer_instance

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Put a continuous function on [0,1] into the native Lp space. The endpoint
extension is used only for representatives and has no effect on its class. -/
def continuousEmbedding : HardyAveragingContinuous.Spec.Space →L[ℂ] Space p :=
  (BoundedContinuousFunction.toLp p intervalMeasure ℂ).comp
    ((BoundedContinuousFunction.compContinuousCLM ℂ ℂ
      (ContinuousMap.projIccCM : C(ℝ, Icc (0 : ℝ) 1))).comp
      (ContinuousMap.linearIsometryBoundedOfCompact (Icc (0 : ℝ) 1) ℂ ℂ).toLinearIsometry.toContinuousLinearMap)

lemma continuousEmbedding_formula (f : HardyAveragingContinuous.Spec.Space) :
    (continuousEmbedding p f : ℝ → ℂ) =ᵐ[intervalMeasure]
      HardyAveragingContinuous.Spec.extension f := by
  exact BoundedContinuousFunction.coeFn_toLp p intervalMeasure ℂ _

lemma continuousEmbedding_denseRange (hpfin : p ≠ ∞) : DenseRange (continuousEmbedding p) := by
  apply (BoundedContinuousFunction.toLp_denseRange ℂ intervalMeasure ℂ hpfin).mono
  rintro _ ⟨f, rfl⟩
  let g : HardyAveragingContinuous.Spec.Space :=
    f.toContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩
  refine ⟨g, ?_⟩
  apply Lp.ext
  filter_upwards [continuousEmbedding_formula p g,
    BoundedContinuousFunction.coeFn_toLp p intervalMeasure ℂ f,
    ae_restrict_mem measurableSet_Ioo] with x hx hf hxm
  rw [hx, hf]
  exact HardyAveragingContinuous.extension_apply g ⟨x, hxm.1.le, hxm.2.le⟩

lemma integral_congr_on_unit {f g : ℝ → ℂ} (hfg : f =ᵐ[intervalMeasure] g)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..x, f t) = ∫ t in (0 : ℝ)..x, g t := by
  apply intervalIntegral.integral_congr_ae'
  · filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp hfg] with t ht htm
    exact ht ⟨htm.1, lt_of_le_of_lt htm.2 hx.2⟩
  · filter_upwards [] with t ht
    exact False.elim ((not_lt_of_ge ht.2) (lt_trans hx.1 ht.1))

lemma hardy_continuousEmbedding (Q : Space p →L[ℂ] Space p) (hQ : IsHardy Q)
    (f : HardyAveragingContinuous.Spec.Space) :
    Q (continuousEmbedding p f) = continuousEmbedding p (HardyAveragingContinuous.hardy f) := by
  apply Lp.ext
  filter_upwards [(hQ (continuousEmbedding p f)).2,
    continuousEmbedding_formula p (HardyAveragingContinuous.hardy f),
    ae_restrict_mem measurableSet_Ioo] with x hx hh hxm
  rw [hx, hh]
  dsimp [Spec.average]
  rw [integral_congr_on_unit (continuousEmbedding_formula p f) hxm,
    HardyAveragingContinuous.extension_apply _ ⟨x, hxm.1.le, hxm.2.le⟩,
    HardyAveragingContinuous.hardy_apply_pos _ _ hxm.1]

lemma weighted_continuousEmbedding (a : ℂ) (ha : a.re < 1)
    (H : Space p →L[ℂ] Space p) (hH : IsWeightedHardy a H)
    (f : HardyAveragingContinuous.Spec.Space) :
    H (continuousEmbedding p f) =
      continuousEmbedding p (HardyAveragingContinuous.weightedAverage a f) := by
  apply Lp.ext
  filter_upwards [(hH (continuousEmbedding p f)).2,
    continuousEmbedding_formula p (HardyAveragingContinuous.weightedAverage a f),
    ae_restrict_mem measurableSet_Ioo] with x hx hh hxm
  rw [hx, hh]
  have hw : (fun t : ℝ => (t : ℂ) ^ (-a) * (continuousEmbedding p f) t) =ᵐ[intervalMeasure]
      (fun t : ℝ => (t : ℂ) ^ (-a) * HardyAveragingContinuous.Spec.extension f t) := by
    filter_upwards [continuousEmbedding_formula p f] with t ht
    rw [ht]
  dsimp [weightedAverage]
  rw [integral_congr_on_unit hw hxm,
    HardyAveragingContinuous.extension_apply _ ⟨x, hxm.1.le, hxm.2.le⟩,
    HardyAveragingContinuous.weightedAverage_apply_pos a ha _ _ hxm.1]

open scoped unitInterval
open HardyAveragingContinuous.Spec in
lemma continuousEmbedding_dilation_ae (f : HardyAveragingContinuous.Spec.Space) (r : I) :
    (continuousEmbedding p (dilation f r) : ℝ → ℂ) =ᵐ[intervalMeasure]
      fun x : ℝ => extension f ((r : ℝ) * x) := by
  filter_upwards [continuousEmbedding_formula p (dilation f r),
    ae_restrict_mem measurableSet_Ioo] with x hx hxm
  rw [hx, HardyAveragingContinuous.extension_apply (dilation f r) ⟨x, hxm.1.le, hxm.2.le⟩]
  exact (HardyAveragingContinuous.extension_apply f (r * ⟨x, hxm.1.le, hxm.2.le⟩)).symm

open HardyAveragingContinuous.Spec in
lemma continuousEmbedding_dilation_norm_le
    (f : HardyAveragingContinuous.Spec.Space) (r : I) (hr : 0 < (r : ℝ)) :
    ‖continuousEmbedding p (dilation f r)‖ ≤
      (r : ℝ) ^ (-(1 / p.toReal)) * ‖continuousEmbedding p f‖ := by
  have hn := dilation_eLpNorm_le (p := p) (extension f) (extension f).continuous.stronglyMeasurable hr r.property.2
  have hf := eLpNorm_congr_ae (p := p) (continuousEmbedding_formula p f)
  have hd := eLpNorm_congr_ae (p := p) (continuousEmbedding_dilation_ae p f r)
  rw [← hf, ← hd] at hn
  have htop : ENNReal.ofReal (r : ℝ)⁻¹ ^ (1 / p).toReal *
      eLpNorm (continuousEmbedding p f) p intervalMeasure ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top).ne
      (Lp.eLpNorm_ne_top _)
  have hn' := ENNReal.toReal_mono htop hn
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hr.le), ENNReal.toReal_div,
    ENNReal.toReal_one, ← Lp.norm_def, Real.inv_rpow hr.le,
    ← Real.rpow_neg hr.le] using hn'

lemma weightedFactor_integrable {p : ℝ≥0∞} (a : ℂ)
    (ha : a.re < threshold p) :
    Integrable (fun r : I => (r : ℝ) ^ (-a.re - 1 / p.toReal)) := by
  have hi : IntervalIntegrable (fun r : ℝ => r ^ (-a.re - 1 / p.toReal)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by dsimp [threshold] at ha; linarith)
  exact (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp
    ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hi)

lemma weightedFactor_integral {p : ℝ≥0∞} (a : ℂ)
    (ha : a.re < threshold p) :
    (∫ r : I, (r : ℝ) ^ (-a.re - 1 / p.toReal)) = 1 / (threshold p - a.re) := by
  rw [integral_subtype measurableSet_Icc (fun r : ℝ => r ^ (-a.re - 1 / p.toReal)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl (by dsimp [threshold] at ha; linarith))]
  rw [Real.one_rpow, Real.zero_rpow (by dsimp [threshold] at ha; linarith), sub_zero]
  congr 1
  dsimp [threshold]
  ring

lemma weightedFactor_mul_eq {p : ℝ≥0∞} (a : ℂ) :
    (fun r : I => (r : ℝ) ^ (-a.re) * (r : ℝ) ^ (-(1 / p.toReal))) =ᵐ[volume]
      (fun r : I => (r : ℝ) ^ (-a.re - 1 / p.toReal)) := by
  filter_upwards [Measure.ae_ne volume (0 : I)] with r hr
  have hr0 : (0 : ℝ) < r := lt_of_le_of_ne r.property.1 (by
    intro h
    apply hr
    exact Subtype.ext h.symm)
  rw [← Real.rpow_add hr0]
  congr 1

lemma weightedFactor_mul_integrable {p : ℝ≥0∞} (a : ℂ)
    (ha : a.re < threshold p) :
    Integrable (fun r : I => (r : ℝ) ^ (-a.re) * (r : ℝ) ^ (-(1 / p.toReal))) := by
  exact (weightedFactor_integrable a ha).congr (weightedFactor_mul_eq a).symm

lemma weightedFactor_mul_integral {p : ℝ≥0∞} (a : ℂ)
    (ha : a.re < threshold p) :
    (∫ r : I, (r : ℝ) ^ (-a.re) * (r : ℝ) ^ (-(1 / p.toReal))) =
      1 / (threshold p - a.re) := by
  rw [integral_congr_ae (weightedFactor_mul_eq a), weightedFactor_integral a ha]

lemma weightedFactor_mul_const_integral {p : ℝ≥0∞} (a : ℂ)
    (ha : a.re < threshold p) (C : ℝ) :
    (∫ r : I, (r : ℝ) ^ (-a.re) * ((r : ℝ) ^ (-(1 / p.toReal)) * C)) =
      (1 / (threshold p - a.re)) * C := by
  simp_rw [← mul_assoc]
  rw [integral_mul_const, weightedFactor_mul_integral a ha]


open HardyAveragingContinuous.Spec in
lemma weighted_continuous_norm_le (a : ℂ) (ha : a.re < threshold p)
    (f : HardyAveragingContinuous.Spec.Space) :
    ‖continuousEmbedding p (HardyAveragingContinuous.weightedAverage a f)‖ ≤
      (1 / (threshold p - a.re)) * ‖continuousEmbedding p f‖ := by
  have ha1 : a.re < 1 := by
    have hnonneg : 0 ≤ 1 / p.toReal := one_div_nonneg.mpr ENNReal.toReal_nonneg
    dsimp [threshold] at ha
    linarith
  have hi := HardyAveragingContinuous.weighted_dilation_integrable a ha1 f
  change ‖continuousEmbedding p (∫ r : I, (r : ℂ) ^ (-a) • dilation f r)‖ ≤ _
  rw [← (continuousEmbedding p).integral_comp_comm hi]
  calc
    ‖∫ r : I, continuousEmbedding p ((r : ℂ) ^ (-a) • dilation f r)‖ ≤
        ∫ r : I, ‖continuousEmbedding p ((r : ℂ) ^ (-a) • dilation f r)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ r : I, (r : ℝ) ^ (-a.re) *
        ((r : ℝ) ^ (-(1 / p.toReal)) * ‖continuousEmbedding p f‖) := by
      have hmajor := (weightedFactor_mul_integrable a ha).mul_const ‖continuousEmbedding p f‖
      simp only [mul_assoc] at hmajor
      apply integral_mono_ae ((continuousEmbedding p).integrable_comp hi).norm hmajor
      filter_upwards [Measure.ae_ne volume (0 : I)] with r hr
      have hr0 : (0 : ℝ) < r := lt_of_le_of_ne r.property.1 (by
        intro h
        apply hr
        exact Subtype.ext h.symm)
      rw [map_smul, norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hr0]
      simpa only [Complex.neg_re] using
        mul_le_mul_of_nonneg_left (continuousEmbedding_dilation_norm_le p f r hr0)
          (Real.rpow_nonneg hr0.le (-a.re))
    _ = (1 / (threshold p - a.re)) * ‖continuousEmbedding p f‖ :=
      weightedFactor_mul_const_integral a ha _


/-- Extend the already-defined continuous weighted integral through its dense
inclusion in Lp. The sharp Lp estimate is a hypothesis to this construction. -/
def weightedExtension (a : ℂ) (ha : a.re < 1) : Space p →L[ℂ] Space p :=
  (((continuousEmbedding p).comp
    (HardyAveragingContinuous.weightedOperator a ha)).toLinearMap).extendOfNorm
      (continuousEmbedding p).toLinearMap

lemma weightedExtension_eq (hpfin : p ≠ ∞) (a : ℂ) (ha : a.re < 1)
    (C : ℝ)
    (hbound : ∀ f : HardyAveragingContinuous.Spec.Space,
      ‖continuousEmbedding p (HardyAveragingContinuous.weightedAverage a f)‖ ≤
        C * ‖continuousEmbedding p f‖)
    (f : HardyAveragingContinuous.Spec.Space) :
    weightedExtension p a ha (continuousEmbedding p f) =
      continuousEmbedding p (HardyAveragingContinuous.weightedAverage a f) := by
  exact LinearMap.extendOfNorm_eq (continuousEmbedding_denseRange p hpfin)
    ⟨C, hbound⟩ f

lemma weightedExtension_norm_le (hpfin : p ≠ ∞) (a : ℂ) (ha : a.re < 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ f : HardyAveragingContinuous.Spec.Space,
      ‖continuousEmbedding p (HardyAveragingContinuous.weightedAverage a f)‖ ≤
        C * ‖continuousEmbedding p f‖) :
    ‖weightedExtension p a ha‖ ≤ C := by
  exact LinearMap.opNorm_extendOfNorm_le
    (continuousEmbedding_denseRange p hpfin) hC hbound


lemma weighted_formula_of_continuous_agreement {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : ℂ) (ha : a.re < 1)
    (H : Space p →L[ℂ] Space p)
    (hH : ∀ g : HardyAveragingContinuous.Spec.Space,
      H (continuousEmbedding p g) = continuousEmbedding p (HardyAveragingContinuous.weightedAverage a g))
    (g : HardyAveragingContinuous.Spec.Space) :
    (H (continuousEmbedding p g) : ℝ → ℂ) =ᵐ[intervalMeasure]
      Spec.weightedAverage a (continuousEmbedding p g : ℝ → ℂ) := by
  rw [hH]
  filter_upwards [continuousEmbedding_formula p (HardyAveragingContinuous.weightedAverage a g),
    ae_restrict_mem measurableSet_Ioo] with x hx hxm
  rw [hx, HardyAveragingContinuous.extension_apply _ ⟨x, hxm.1.le, hxm.2.le⟩,
    HardyAveragingContinuous.weightedAverage_apply_pos a ha _ _ hxm.1]
  have hw : (fun t : ℝ => (t : ℂ) ^ (-a) * (continuousEmbedding p g) t) =ᵐ[intervalMeasure]
      (fun t : ℝ => (t : ℂ) ^ (-a) * HardyAveragingContinuous.Spec.extension g t) := by
    filter_upwards [continuousEmbedding_formula p g] with t ht
    rw [ht]
  dsimp [Spec.weightedAverage]
  rw [integral_congr_on_unit hw hxm]

lemma weighted_isHardy_of_dense {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hpfin : p ≠ ∞) (a : ℂ) (ha : a.re < threshold p)
    (H : Space p →L[ℂ] Space p)
    (hH : ∀ g : HardyAveragingContinuous.Spec.Space,
      H (continuousEmbedding p g) = continuousEmbedding p (HardyAveragingContinuous.weightedAverage a g))
    (heval : ∀ x ∈ Ioo (0 : ℝ) 1,
      Continuous (fun f : Space p => Spec.weightedAverage a (f : ℝ → ℂ) x)) :
    IsWeightedHardy a H := by
  intro f
  refine ⟨weighted_primitive_integrable hp hpfin a ha f, ?_⟩
  obtain ⟨u, hu, hut⟩ := mem_closure_iff_seq_limit.mp (continuousEmbedding_denseRange p hpfin f)
  have ha1 : a.re < 1 := by
    have hp0 : 0 < p.toReal := lt_trans zero_lt_one (toReal_gt_one hp hpfin)
    exact lt_trans ha (sub_lt_self 1 (one_div_pos.mpr hp0))
  have hn : ∀ n : ℕ, (H (u n) : ℝ → ℂ) =ᵐ[intervalMeasure]
      Spec.weightedAverage a (u n : ℝ → ℂ) := by
    intro n
    obtain ⟨g, hg⟩ := hu n
    rw [← hg]
    exact weighted_formula_of_continuous_agreement a ha1 H hH g
  have hHt : Filter.Tendsto (fun n => H (u n)) Filter.atTop (𝓝 (H f)) :=
    H.continuous.continuousAt.tendsto.comp hut
  obtain ⟨ns, hns, hnsAe⟩ := (tendstoInMeasure_of_tendsto_Lp hHt).exists_seq_tendsto_ae
  filter_upwards [hnsAe, ae_all_iff.mpr hn, ae_restrict_mem measurableSet_Ioo]
    with x hx heq hxm
  have ht := ((heval x hxm).tendsto f).comp (hut.comp hns.tendsto_atTop)
  apply tendsto_nhds_unique hx
  exact ht.congr' (Filter.Eventually.of_forall fun n => (heq (ns n)).symm)


end ContinuousBridge

/-- Weighted Hardy averaging exists on the native complex Lp space with the
required quantitative bound. Its construction extends the actual continuous
integral and the Hölder evaluation functionals identify every Lp image. -/
theorem weighted_operator_existence : Spec.WeightedOperatorExistence := by
  intro p _ hp hpfin a ha
  have ha1 : a.re < 1 := by
    have hnonneg : 0 ≤ 1 / p.toReal := one_div_nonneg.mpr ENNReal.toReal_nonneg
    dsimp [threshold] at ha
    linarith
  let H := weightedExtension p a ha1
  have hbound := weighted_continuous_norm_le p a ha
  have hagree := weightedExtension_eq p hpfin a ha1
    (1 / (threshold p - a.re)) hbound
  refine ⟨H, ?_, ?_⟩
  · exact weighted_isHardy_of_dense hp hpfin a ha H hagree
      (fun _ hx => weightedAverage_continuous hp hpfin a ha hx)
  · exact weightedExtension_norm_le p hpfin a ha1
      (1 / (threshold p - a.re)) (one_div_pos.mpr (sub_pos.mpr ha)).le hbound

section Assembly

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma hardy_unique (Q R : Space p →L[ℂ] Space p) (hQ : IsHardy Q) (hR : IsHardy R) :
    Q = R := by
  apply ContinuousLinearMap.ext
  intro f
  exact Lp.ext ((hQ f).2.trans (hR f).2.symm)

def exteriorInverse (z : ℂ) (H : Space p →L[ℂ] Space p) : Space p →L[ℂ] Space p :=
  (-z⁻¹) • ContinuousLinearMap.id ℂ (Space p) - z⁻¹ ^ 2 • H

lemma exteriorInverse_right (z : ℂ) (hz : z ≠ 0) (Q H : Space p →L[ℂ] Space p)
    (hc : ∀ f, z⁻¹ • Q (H f) = H f - Q f) (f : Space p) :
    Q (exteriorInverse z H f) - z • exteriorInverse z H f = f := by
  change Q ((-z⁻¹) • f - z⁻¹ ^ 2 • H f) -
    z • ((-z⁻¹) • f - z⁻¹ ^ 2 • H f) = f
  calc
    _ = (-z⁻¹) • Q f - z⁻¹ • (z⁻¹ • Q (H f)) + (z * z⁻¹) • f +
        ((z * z⁻¹) * z⁻¹) • H f := by
      simp only [map_sub, map_smul]
      module
    _ = f := by rw [hc, mul_inv_cancel₀ hz]; module

lemma exteriorInverse_left (z : ℂ) (hz : z ≠ 0) (Q H : Space p →L[ℂ] Space p)
    (hc : ∀ f, z⁻¹ • H (Q f) = H f - Q f) (f : Space p) :
    exteriorInverse z H (Q f - z • f) = f := by
  change (-z⁻¹) • (Q f - z • f) - z⁻¹ ^ 2 • H (Q f - z • f) = f
  calc
    _ = (-z⁻¹) • Q f + (z * z⁻¹) • f - z⁻¹ • (z⁻¹ • H (Q f)) +
        ((z * z⁻¹) * z⁻¹) • H f := by
      simp only [map_sub, map_smul]
      module
    _ = f := by rw [hc, mul_inv_cancel₀ hz]; module

lemma exteriorInverse_bound (z : ℂ) (H : Space p →L[ℂ] Space p)
    (ha : (z⁻¹).re < threshold p) (hbound : ‖H‖ ≤ 1 / (threshold p - (z⁻¹).re)) :
    ‖exteriorInverse z H‖ ≤ ‖z⁻¹‖ + ‖z⁻¹‖ ^ 2 / (threshold p - (z⁻¹).re) := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg (norm_nonneg _) (div_nonneg (sq_nonneg _) (sub_pos.mpr ha).le))
  intro f
  change ‖(-z⁻¹) • f - z⁻¹ ^ 2 • H f‖ ≤ _
  calc
    _ ≤ ‖(-z⁻¹) • f‖ + ‖z⁻¹ ^ 2 • H f‖ := norm_sub_le _ _
    _ = ‖z⁻¹‖ * ‖f‖ + ‖z⁻¹‖ ^ 2 * ‖H f‖ := by
      rw [norm_smul, norm_smul, norm_neg, norm_pow]
    _ ≤ ‖z⁻¹‖ * ‖f‖ + ‖z⁻¹‖ ^ 2 *
        ((1 / (threshold p - (z⁻¹).re)) * ‖f‖) := by
      gcongr
      exact (H.le_opNorm f).trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg f))
    _ = _ := by ring

lemma exteriorInverse_formula (z : ℂ) (H : Space p →L[ℂ] Space p)
    (hH : IsWeightedHardy z⁻¹ H) (f : Space p) :
    (exteriorInverse z H f : ℝ → ℂ) =ᵐ[intervalMeasure]
      fun x => -z⁻¹ * f x - z⁻¹ ^ 2 * weightedAverage z⁻¹ (f : ℝ → ℂ) x := by
  change ((-z⁻¹) • f - z⁻¹ ^ 2 • H f : Space p) =ᵐ[intervalMeasure] _
  filter_upwards [Lp.coeFn_sub ((-z⁻¹) • f) (z⁻¹ ^ 2 • H f),
    Lp.coeFn_smul (-z⁻¹) f, Lp.coeFn_smul (z⁻¹ ^ 2) (H f), (hH f).2] with x hs hf hh hw
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hs hf hh
  rw [hs, hf, hh, hw]

lemma exteriorInverse_continuousEmbedding (z : ℂ) (ha : (z⁻¹).re < 1)
    (H : Space p →L[ℂ] Space p) (hH : IsWeightedHardy z⁻¹ H)
    (f : HardyAveragingContinuous.Spec.Space) :
    exteriorInverse z H (continuousEmbedding p f) =
      continuousEmbedding p (HardyAveragingContinuous.exteriorInverse z ha f) := by
  change (-z⁻¹) • continuousEmbedding p f - z⁻¹ ^ 2 • H (continuousEmbedding p f) =
    continuousEmbedding p ((-z⁻¹) • f - z⁻¹ ^ 2 • HardyAveragingContinuous.weightedAverage z⁻¹ f)
  rw [weighted_continuousEmbedding p z⁻¹ ha H hH f, map_sub, map_smul, map_smul]

/-- Transfer the inverse identities from the accepted continuous-space operator
on a dense subspace. Boundedness of Q and H permits extension to every Lp class. -/
lemma exteriorInverse_identities (hp : 1 < p) (hpfin : p ≠ ∞)
    (Q : Space p →L[ℂ] Space p) (hQ : IsHardy Q)
    (z : ℂ) (hz : z ≠ 0) (ha : (z⁻¹).re < threshold p)
    (H : Space p →L[ℂ] Space p) (hH : IsWeightedHardy z⁻¹ H) :
    (∀ f, exteriorInverse z H (Q f - z • f) = f) ∧
      (∀ f, Q (exteriorInverse z H f) - z • exteriorInverse z H f = f) := by
  have hc : (z⁻¹).re < 1 := by
    have hp0 : 0 < p.toReal := lt_trans zero_lt_one (toReal_gt_one hp hpfin)
    exact lt_trans ha (sub_lt_self 1 (one_div_pos.mpr hp0))
  have hd := continuousEmbedding_denseRange p hpfin
  let T : Space p →L[ℂ] Space p := Q - z • ContinuousLinearMap.id ℂ (Space p)
  let R := exteriorInverse z H
  have hl : ∀ f : Space p, R (T f) = f := by
    intro f
    refine hd.induction_on (p := fun f : Space p => R (T f) = f) f
      (isClosed_eq (R.continuous.comp T.continuous) continuous_id) ?_
    intro g
    change exteriorInverse z H (Q (continuousEmbedding p g) - z • continuousEmbedding p g) = _
    rw [hardy_continuousEmbedding p Q hQ,
      ← map_smul (continuousEmbedding p) z g, ← map_sub,
      exteriorInverse_continuousEmbedding z hc H hH]
    exact congrArg (continuousEmbedding p)
      (HardyAveragingContinuous.exteriorInverse_left z hz hc g)
  have hr : ∀ f : Space p, T (R f) = f := by
    intro f
    refine hd.induction_on (p := fun f : Space p => T (R f) = f) f
      (isClosed_eq (T.continuous.comp R.continuous) continuous_id) ?_
    intro g
    change Q (exteriorInverse z H (continuousEmbedding p g)) -
      z • exteriorInverse z H (continuousEmbedding p g) = _
    rw [exteriorInverse_continuousEmbedding z hc H hH,
      hardy_continuousEmbedding p Q hQ,
      ← map_smul (continuousEmbedding p), ← map_sub]
    exact congrArg (continuousEmbedding p)
      (HardyAveragingContinuous.exteriorInverse_right z hz hc g)
  exact ⟨hl, hr⟩

lemma eigenvalue_mem_spectrum (Q : Space p →L[ℂ] Space p) (z : ℂ)
    (f : Space p) (hf : f ≠ 0) (he : Q f = z • f) : z ∈ spectrum ℂ Q := by
  change z ∈ Specs.ExpandedFA.BanachAlgebra.Conventions.AlgebraSpectrumValue
    ℂ (Space p →L[ℂ] Space p) Q
  rw [BanachAlgebra.operator_spectrum_iff_no_bounded_inverse]
  rintro ⟨S, hleft, _⟩
  have h := hleft f
  rw [he, sub_self, map_zero] at h
  exact hf h.symm

lemma closed_disk_subset_spectrum (hp : 1 < p) (hpfin : p ≠ ∞)
    (Q : Space p →L[ℂ] Space p) (heig : Spec.EigenvalueDisk Q) :
    {z : ℂ | ‖z - (conjugateExponent p / 2 : ℝ)‖ ≤ conjugateExponent p / 2} ⊆
      spectrum ℂ Q := by
  have hball : Metric.ball ((conjugateExponent p / 2 : ℝ) : ℂ)
      (conjugateExponent p / 2) ⊆ spectrum ℂ Q := by
    intro z hz
    have hmem : z ∈ {z : ℂ | ‖z - (conjugateExponent p / 2 : ℝ)‖ <
        conjugateExponent p / 2} := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    rw [← heig] at hmem
    obtain ⟨f, hf, he⟩ := hmem
    exact eigenvalue_mem_spectrum Q z f hf he
  have hcl := closure_minimal hball (spectrum.isClosed (𝕜 := ℂ) Q)
  rw [closure_ball _ (ne_of_gt (half_pos (conjugateExponent_pos hp hpfin)))] at hcl
  simpa only [Metric.closedBall, dist_eq_norm] using hcl

lemma norm_exact_of_eigenvalue_disk (hp : 1 < p) (hpfin : p ≠ ∞)
    (Q : Space p →L[ℂ] Space p) (heig : Spec.EigenvalueDisk Q)
    (hbound : ‖Q‖ ≤ conjugateExponent p) : Spec.NormExact Q := by
  apply le_antisymm hbound
  have hd := conjugateExponent_pos hp hpfin
  have hmem : (conjugateExponent p : ℂ) ∈ spectrum ℂ Q := by
    apply closed_disk_subset_spectrum hp hpfin Q heig
    change ‖(conjugateExponent p : ℂ) - ((conjugateExponent p / 2 : ℝ) : ℂ)‖ ≤ _
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ conjugateExponent p - conjugateExponent p / 2)]
    linarith
  have h := spectrum.norm_le_norm_mul_of_mem hmem
  have hid : ‖(1 : Space p →L[ℂ] Space p)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hbound' := h.trans (mul_le_of_le_one_right (norm_nonneg Q) hid)
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd] using hbound'

lemma spectrum_disk_of_eigenvalues_and_resolvent (hp : 1 < p) (hpfin : p ≠ ∞)
    (Q : Space p →L[ℂ] Space p) (heig : Spec.EigenvalueDisk Q)
    (hres : Spec.ExteriorResolvent Q) : Spec.SpectrumDisk Q := by
  apply Subset.antisymm _ (closed_disk_subset_spectrum hp hpfin Q heig)
  intro z hz
  by_contra hout
  have hnorm : conjugateExponent p / 2 <
      ‖z - ((conjugateExponent p / 2 : ℝ) : ℂ)‖ := lt_of_not_ge hout
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    have hd := conjugateExponent_pos hp hpfin
    simp only [zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hd)] at hnorm
    exact (lt_irrefl _ hnorm)
  have ha : (z⁻¹).re < threshold p :=
    (inverse_re_lt_iff_exterior (threshold p) (threshold_pos hp hpfin) z hz0).mpr hnorm
  obtain ⟨R, hleft, hright, _⟩ := hres z hz0 ha
  change z ∈ Specs.ExpandedFA.BanachAlgebra.Conventions.AlgebraSpectrumValue
    ℂ (Space p →L[ℂ] Space p) Q at hz
  rw [BanachAlgebra.operator_spectrum_iff_no_bounded_inverse] at hz
  apply hz
  refine ⟨-R, ?_, ?_⟩
  · intro f
    change -R (z • f - Q f) = f
    rw [← neg_sub (Q f), map_neg, neg_neg]
    exact hleft f
  · intro f
    change z • -R f - Q (-R f) = f
    rw [map_neg, smul_neg, sub_neg_eq_add, neg_add_eq_sub]
    exact hright f

lemma noncompact_of_eigenvalue_disk (hp : 1 < p) (hpfin : p ≠ ∞)
    (Q : Space p →L[ℂ] Space p) (heig : Spec.EigenvalueDisk Q) : Spec.Noncompact Q := by
  intro hc
  have hd := conjugateExponent_pos hp hpfin
  have hcompact : Compactness.IsCompactLinearMap Q.toLinearMap :=
    (Compactness.compact_iff_isCompactOperator _).mpr hc
  have hfin := Fredholm.compact_eigenvalues_finite_away_from_zero Q hcompact
    (conjugateExponent p / 2) (half_pos hd)
  have hm : MapsTo (fun r : ℝ => (r : ℂ))
      (Ioo (conjugateExponent p / 2) (conjugateExponent p))
      {z : ℂ | (∃ f : Space p, f ≠ 0 ∧ Q f = z • f) ∧
        conjugateExponent p / 2 ≤ ‖z‖} := by
    intro r hr
    have hrpos : 0 < r := lt_trans (half_pos hd) hr.1
    constructor
    · have hmem : (r : ℂ) ∈ {z : ℂ | ‖z - (conjugateExponent p / 2 : ℝ)‖ <
          conjugateExponent p / 2} := by
        change ‖(r : ℂ) - ((conjugateExponent p / 2 : ℝ) : ℂ)‖ < _
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (sub_pos.mpr hr.1)]
        linarith [hr.2]
      rw [← heig] at hmem
      exact hmem
    · simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos] using hr.1.le
  exact (Ioo_infinite (by linarith : conjugateExponent p / 2 < conjugateExponent p))
    (hfin.of_injOn hm (by intro r _ s _ h; exact Complex.ofReal_injective h))

end Assembly

/-- Complete formal assembly once the three explicitly separated analytic
interfaces have been proved. This conditional result is not `FullResult`. -/
theorem assembly : Spec.Assembly := by
  intro hconstruct heigen hres p _ hp hpfin
  refine ⟨power_membership hp hpfin, ?_⟩
  obtain ⟨Q, hQ, hbound⟩ := hconstruct p hp hpfin
  obtain ⟨hinj, hpower, heig⟩ := heigen p hp hpfin Q hQ
  have hR := hres p hp hpfin Q hQ
  exact ⟨Q, hQ, norm_exact_of_eigenvalue_disk hp hpfin Q heig hbound,
    hpower, heig, hinj, hR, spectrum_disk_of_eigenvalues_and_resolvent hp hpfin Q heig hR,
    noncompact_of_eigenvalue_disk hp hpfin Q heig⟩

theorem exterior_resolvent_of_weighted_composition
    (hweighted : Spec.WeightedOperatorExistence) (hcomp : Spec.WeightedCompositionTheorem) :
    Spec.ExteriorResolventTheorem := by
  intro p _ hp hpfin Q hQ z hz ha
  obtain ⟨H, hH, hbound⟩ := hweighted p hp hpfin z⁻¹ ha
  have hC := hcomp p hp hpfin z⁻¹ (inv_ne_zero hz) ha Q H hQ hH
  refine ⟨exteriorInverse z H, ?_, ?_, ?_, exteriorInverse_bound z H ha hbound⟩
  · exact exteriorInverse_left z hz Q H (fun f => (hC f).2)
  · exact exteriorInverse_right z hz Q H (fun f => (hC f).1)
  · intro f
    exact ⟨(hH f).1, exteriorInverse_formula z H hH f⟩

/-- Only the weighted operator construction and its estimate remain analytic
inputs. The inverse equations follow by the proved continuous-density bridge. -/
theorem exterior_resolvent_of_weighted_existence (hw : Spec.WeightedOperatorExistence) :
    Spec.ExteriorResolventTheorem := by
  intro p _ hp hpfin Q hQ z hz ha
  obtain ⟨H, hH, hbound⟩ := hw p hp hpfin z⁻¹ ha
  obtain ⟨hleft, hright⟩ := exteriorInverse_identities hp hpfin Q hQ z hz ha H hH
  exact ⟨exteriorInverse z H, hleft, hright,
    fun f => ⟨(hH f).1, exteriorInverse_formula z H hH f⟩,
    exteriorInverse_bound z H ha hbound⟩

theorem operator_existence_of_weighted (hw : Spec.WeightedOperatorExistence) :
    Spec.OperatorExistence := by
  intro p _ hp hpfin
  obtain ⟨Q, hQ, hbound⟩ := hw p hp hpfin 0 (by
    simpa only [Complex.zero_re] using threshold_pos hp hpfin)
  refine ⟨Q, ?_, ?_⟩
  · intro f
    constructor
    · simpa only [neg_zero, Complex.cpow_zero, one_mul] using (hQ f).1
    · have h := (hQ f).2
      change (Q f : ℝ → ℂ) =ᵐ[intervalMeasure]
        (fun x => (x : ℂ) ^ (0 - 1 : ℂ) *
          ∫ t in (0 : ℝ)..x, (t : ℂ) ^ (-(0 : ℂ)) * f t) at h
      change (Q f : ℝ → ℂ) =ᵐ[intervalMeasure]
        (fun x => (x : ℂ)⁻¹ * ∫ t in (0 : ℝ)..x, f t)
      simpa only [neg_zero, Complex.cpow_zero,
        one_mul, zero_sub, Complex.cpow_neg_one] using h
  · simpa only [Complex.zero_re, sub_zero, one_div, conjugateExponent] using hbound

/-- All original conclusions now follow from the sole remaining analytic input:
the construction and sharp upper bound for weighted averaging on Lp. -/
theorem weighted_assembly : Spec.WeightedAssembly := by
  intro hw
  exact assembly (operator_existence_of_weighted hw) eigenfunction_theorem
    (exterior_resolvent_of_weighted_existence hw)

/-- Final assembly with the remaining analytic obligations isolated.
No asserted existence or Fubini identity is assumed in a definition. -/
theorem analytic_assembly : Spec.AnalyticAssembly := by
  rintro ⟨hconstruct, hweighted⟩ heigen hcomp
  exact assembly hconstruct heigen (exterior_resolvent_of_weighted_composition hweighted hcomp)

/-- The complete Lp conclusion of the adopted Hardy averaging theorem. -/
theorem full_result : Spec.FullResult :=
  weighted_assembly weighted_operator_existence



/-! Real-valued Lp and its genuine inclusion into the complex model. -/

section RealForm

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The pointwise inclusion of real-valued Lp into complex-valued Lp. -/
def realInclusion : RealSpace p →ₗᵢ[ℝ] Space p where
  toLinearMap := Complex.ofRealCLM.compLpₗ p intervalMeasure
  norm_map' f := by
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    change eLpNorm (Complex.ofRealCLM.compLp f) p intervalMeasure = eLpNorm f p intervalMeasure
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable f)
    filter_upwards [Complex.ofRealCLM.coeFn_compLp f] with x hx
    rw [hx]
    exact Complex.norm_real (f x)

def realPart : Space p →L[ℝ] RealSpace p :=
  Complex.reCLM.compLpL p intervalMeasure

def imagPart : Space p →L[ℝ] RealSpace p :=
  Complex.imCLM.compLpL p intervalMeasure

lemma realInclusion_ae (f : RealSpace p) :
    (realInclusion p f : ℝ → ℂ) =ᵐ[intervalMeasure] fun x => (f x : ℂ) :=
  Complex.ofRealCLM.coeFn_compLp f

lemma realPart_ae (f : Space p) :
    (realPart p f : ℝ → ℝ) =ᵐ[intervalMeasure] fun x => (f x).re :=
  Complex.reCLM.coeFn_compLp f

lemma imagPart_ae (f : Space p) :
    (imagPart p f : ℝ → ℝ) =ᵐ[intervalMeasure] fun x => (f x).im :=
  Complex.imCLM.coeFn_compLp f

/-- The ordinary real and imaginary decomposition of complex Lp. -/
def realForm : HardyAveragingRealBridge.RealForm (RealSpace p) (Space p) where
  inclusion := realInclusion p
  re := realPart p
  im := imagPart p
  re_inclusion f := by
    change realPart p (realInclusion p f) = f
    apply Lp.ext
    filter_upwards [realPart_ae p (realInclusion p f), realInclusion_ae p f] with x hx hi
    simp only [hx, hi, Complex.ofReal_re]
  im_inclusion f := by
    change imagPart p (realInclusion p f) = 0
    apply Lp.ext
    filter_upwards [imagPart_ae p (realInclusion p f), realInclusion_ae p f,
      Lp.coeFn_zero ℝ p intervalMeasure] with x hx hi hz
    simp only [hx, hi, hz, Complex.ofReal_im, Pi.zero_apply]
  re_I_inclusion f := by
    change realPart p (Complex.I • realInclusion p f) = 0
    apply Lp.ext
    filter_upwards [realPart_ae p (Complex.I • realInclusion p f),
      Lp.coeFn_smul Complex.I (realInclusion p f), realInclusion_ae p f,
      Lp.coeFn_zero ℝ p intervalMeasure] with x hx hs hi hz
    calc
      _ = 0 := by simp [hx, hs, hi]
      _ = _ := (show ((0 : RealSpace p) : ℝ → ℝ) x = 0 by simpa using hz).symm
  im_I_inclusion f := by
    change imagPart p (Complex.I • realInclusion p f) = f
    apply Lp.ext
    filter_upwards [imagPart_ae p (Complex.I • realInclusion p f),
      Lp.coeFn_smul Complex.I (realInclusion p f), realInclusion_ae p f] with x hx hs hi
    simp [hx, hs, hi]
  reconstruct f := by
    change f = realInclusion p (realPart p f) + Complex.I • realInclusion p (imagPart p f)
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (realInclusion p (realPart p f))
        (Complex.I • realInclusion p (imagPart p f)),
      realInclusion_ae p (realPart p f), realInclusion_ae p (imagPart p f),
      Lp.coeFn_smul Complex.I (realInclusion p (imagPart p f)),
      realPart_ae p f, imagPart_ae p f] with x ha hr hi hs hfr hfi
    simp only [Pi.add_apply] at ha
    simp only [Pi.smul_apply] at hs
    rw [ha, hr, hs, hi, hfr, hfi]
    simpa only [smul_eq_mul, mul_comm Complex.I] using (Complex.re_add_im (f x)).symm

lemma realForm_inclusion_ae (f : RealSpace p) :
    ((realForm p).inclusion f : ℝ → ℂ) =ᵐ[intervalMeasure] fun x => (f x : ℂ) :=
  realInclusion_ae p f

lemma realForm_re_ae (f : Space p) :
    ((realForm p).re f : ℝ → ℝ) =ᵐ[intervalMeasure] fun x => (f x).re :=
  realPart_ae p f

lemma realForm_im_ae (f : Space p) :
    ((realForm p).im f : ℝ → ℝ) =ᵐ[intervalMeasure] fun x => (f x).im :=
  imagPart_ae p f

end RealForm

open HardyAveragingRealBridge

section RealOperator
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : IsFiniteMeasure intervalMeasure := by
  dsimp [intervalMeasure]
  infer_instance

/-- The real operator acts on real-valued equivalence classes. -/
def realHardyOperator (F : RealForm (RealSpace p) (Space p))
    (Q : Space p →L[ℂ] Space p) : RealSpace p →L[ℝ] RealSpace p :=
  F.re.comp ((Q.restrictScalars ℝ).comp F.inclusion.toContinuousLinearMap)

lemma hardy_real_inclusion_formula (F : RealForm (RealSpace p) (Space p))
    (hinc : ∀ f : RealSpace p,
      (F.inclusion f : ℝ → ℂ) =ᵐ[intervalMeasure] fun t => (f t : ℂ))
    (Q : Space p →L[ℂ] Space p) (hQ : IsHardy Q) (f : RealSpace p) :
    (Q (F.inclusion f) : ℝ → ℂ) =ᵐ[intervalMeasure]
      fun x => ((x⁻¹ * ∫ t in (0 : ℝ)..x, f t : ℝ) : ℂ) := by
  filter_upwards [(hQ (F.inclusion f)).2, ae_restrict_mem measurableSet_Ioo] with x hx hxm
  have hi : (∫ t in (0 : ℝ)..x, F.inclusion f t) =
      ∫ t in (0 : ℝ)..x, (f t : ℂ) := by
    apply intervalIntegral.integral_congr_ae'
    · filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp (hinc f)] with t ht htm
      exact ht ⟨htm.1, lt_of_le_of_lt htm.2 hxm.2⟩
    · filter_upwards [] with t ht
      exact False.elim ((not_lt_of_ge ht.2) (lt_trans hxm.1 ht.1))
  rw [hx]
  dsimp [Spec.average]
  rw [hi, intervalIntegral.integral_ofReal]
  simp only [Complex.ofReal_mul, Complex.ofReal_inv]

lemma realHardyOperator_isHardy (F : RealForm (RealSpace p) (Space p))
    (hinc : ∀ f : RealSpace p,
      (F.inclusion f : ℝ → ℂ) =ᵐ[intervalMeasure] fun t => (f t : ℂ))
    (hre : ∀ g : Space p,
      (F.re g : ℝ → ℝ) =ᵐ[intervalMeasure] fun t => (g t).re)
    (Q : Space p →L[ℂ] Space p) (hQ : IsHardy Q) :
    IsRealHardy (realHardyOperator F Q) := by
  intro f
  constructor
  · intro x hx
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hx.1.le).mpr
    have hint : Integrable (f : ℝ → ℝ) intervalMeasure :=
      (Lp.memLp f).integrable (Fact.out : 1 ≤ p)
    change IntegrableOn (f : ℝ → ℝ) (Ioo (0 : ℝ) 1) volume at hint
    exact hint.mono_set (Ioo_subset_Ioo_right hx.2)
  · change (F.re (Q (F.inclusion f)) : ℝ → ℝ) =ᵐ[intervalMeasure] _
    filter_upwards [hre (Q (F.inclusion f)), hardy_real_inclusion_formula F hinc Q hQ f]
      with x hx heq
    rw [hx, heq, Complex.ofReal_re]

lemma realHardyOperator_intertwines (F : RealForm (RealSpace p) (Space p))
    (hinc : ∀ f : RealSpace p,
      (F.inclusion f : ℝ → ℂ) =ᵐ[intervalMeasure] fun t => (f t : ℂ))
    (hre : ∀ g : Space p,
      (F.re g : ℝ → ℝ) =ᵐ[intervalMeasure] fun t => (g t).re)
    (Q : Space p →L[ℂ] Space p) (hQ : IsHardy Q) (f : RealSpace p) :
    Q (F.inclusion f) = F.inclusion (realHardyOperator F Q f) := by
  apply Lp.ext
  filter_upwards [hardy_real_inclusion_formula F hinc Q hQ f,
    hinc (realHardyOperator F Q f),
    (realHardyOperator_isHardy F hinc hre Q hQ f).2] with x hx hi hr
  rw [hx, hi, hr]

lemma real_hardy_unique (Q R : RealSpace p →L[ℝ] RealSpace p)
    (hQ : IsRealHardy Q) (hR : IsRealHardy R) : Q = R := by
  apply ContinuousLinearMap.ext
  intro f
  exact Lp.ext ((hQ f).2.trans (hR f).2.symm)
end RealOperator

lemma real_closed_disk_section (d : ℝ) :
    {t : ℝ | ‖(t : ℂ) - ((d / 2 : ℝ) : ℂ)‖ ≤ d / 2} = Icc 0 d := by
  ext t
  simp only [Set.mem_ofPred_eq, mem_Icc, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

lemma real_open_disk_section (d : ℝ) :
    {t : ℝ | ‖(t : ℂ) - ((d / 2 : ℝ) : ℂ)‖ < d / 2} = Ioo 0 d := by
  ext t
  simp only [Set.mem_ofPred_eq, mem_Ioo, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_lt]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

section RealAssembly

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
  (F : HardyAveragingRealBridge.RealForm (RealSpace p) (Space p))
  (QR : RealSpace p →L[ℝ] RealSpace p) (QC : Space p →L[ℂ] Space p)
  (h : ∀ x, QC (F.inclusion x) = F.inclusion (QR x))

include F h

lemma real_spectrum_of_complex_disk (hs : Spec.SpectrumDisk QC) :
    spectrum ℝ QR = Icc (0 : ℝ) (conjugateExponent p) := by
  rw [HardyAveragingRealBridge.spectrum_transport F QR QC h]
  change spectrum ℂ QC = _ at hs
  rw [hs]
  exact real_closed_disk_section _

lemma real_eigenvalues_of_complex_disk (he : Spec.EigenvalueDisk QC) :
    {t : ℝ | ∃ f : RealSpace p, f ≠ 0 ∧ QR f = t • f} =
      Ioo (0 : ℝ) (conjugateExponent p) := by
  calc
    {t : ℝ | ∃ f : RealSpace p, f ≠ 0 ∧ QR f = t • f} =
        {t : ℝ | ∃ f : Space p, f ≠ 0 ∧ QC f = (t : ℂ) • f} := by
      ext t
      exact HardyAveragingRealBridge.eigenvalue_transport F QR QC h t
    _ = {t : ℝ | ‖(t : ℂ) - ((conjugateExponent p / 2 : ℝ) : ℂ)‖ <
        conjugateExponent p / 2} := by
      ext t
      exact Set.ext_iff.mp he (t : ℂ)
    _ = Ioo 0 (conjugateExponent p) := real_open_disk_section _

lemma real_norm_of_complex_disk (hp : 1 < p) (hpfin : p ≠ ∞)
    (hn : Spec.NormExact QC) (hs : Spec.SpectrumDisk QC) :
    ‖QR‖ = conjugateExponent p := by
  change ‖QC‖ = conjugateExponent p at hn
  apply le_antisymm
  · exact (HardyAveragingRealBridge.norm_bounds_of_intertwines F QR QC h).1.trans_eq hn
  · have hd := conjugateExponent_pos hp hpfin
    have hmem : conjugateExponent p ∈ spectrum ℝ QR := by
      rw [real_spectrum_of_complex_disk F QR QC h hs]
      exact ⟨hd.le, le_rfl⟩
    have hb := spectrum.norm_le_norm_mul_of_mem hmem
    have hid : ‖(1 : RealSpace p →L[ℝ] RealSpace p)‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    have hb' := hb.trans (mul_le_of_le_one_right (norm_nonneg QR) hid)
    simpa only [Real.norm_eq_abs, abs_of_pos hd] using hb'

lemma real_conclusions_of_complex (hp : 1 < p) (hpfin : p ≠ ∞)
    (hn : Spec.NormExact QC) (he : Spec.EigenvalueDisk QC)
    (hi : Spec.NoZeroEigenvalue QC) (hs : Spec.SpectrumDisk QC)
    (hc : Spec.Noncompact QC) :
    ‖QR‖ = conjugateExponent p ∧
      spectrum ℝ QR = Icc (0 : ℝ) (conjugateExponent p) ∧
      {t : ℝ | ∃ f : RealSpace p, f ≠ 0 ∧ QR f = t • f} =
        Ioo (0 : ℝ) (conjugateExponent p) ∧
      Function.Injective QR ∧ ¬ IsCompactOperator QR := by
  refine ⟨real_norm_of_complex_disk F QR QC h hp hpfin hn hs,
    real_spectrum_of_complex_disk F QR QC h hs,
    real_eigenvalues_of_complex_disk F QR QC h he, ?_, ?_⟩
  · intro x y hxy
    apply F.inclusion.injective
    apply hi
    rw [h, h, hxy]
  · intro hQR
    exact hc ((HardyAveragingRealBridge.compact_iff_of_intertwines F QR QC h).mp hQR)

end RealAssembly

/-- The intrinsic real Hardy theorem on the original space of real-valued Lp classes. -/
theorem real_full_result : Spec.RealFullResult := by
  intro p _ hp hpfin
  obtain ⟨_, QC, hQ, hn, _, he, hi, _, hs, hc⟩ := full_result p hp hpfin
  let F := realForm p
  let QR := realHardyOperator F QC
  have hQR : IsRealHardy QR := realHardyOperator_isHardy F
    (realForm_inclusion_ae p) (realForm_re_ae p) QC hQ
  have hcomm : ∀ f, QC (F.inclusion f) = F.inclusion (QR f) :=
    realHardyOperator_intertwines F (realForm_inclusion_ae p) (realForm_re_ae p) QC hQ
  obtain ⟨hnR, hsR, heR, hiR, hcR⟩ :=
    real_conclusions_of_complex F QR QC hcomm hp hpfin hn he hi hs hc
  refine ⟨QR, hQR, hnR, hsR, heR, hiR, hcR, ?_⟩
  intro U hU
  exact real_hardy_unique U QR hU hQR

end ExpandedFA.PartV.HardyAveragingLp
