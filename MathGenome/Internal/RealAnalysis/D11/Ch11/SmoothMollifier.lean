import MathGenome.Internal.RealAnalysis.Specs.D11.Ch11.SmoothMollifier
import MathGenome.Internal.RealAnalysis.D11.Ch03.LebesgueMeasures
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Convolution

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace D11.Ch11.SmoothMollifier
open D11.Ch03 D11.Ch03.LebesgueMeasures
open Specs.D11.Ch03.LebesgueMeasures

abbrev rawBump : Specs.D11.Ch11.SmoothMollifier.rawBump_type :=
  Specs.D11.Ch11.SmoothMollifier.rawBump_value
abbrev mollifier : Specs.D11.Ch11.SmoothMollifier.mollifier_type :=
  Specs.D11.Ch11.SmoothMollifier.mollifier_value
abbrev scaledMollifier : Specs.D11.Ch11.SmoothMollifier.scaledMollifier_type :=
  Specs.D11.Ch11.SmoothMollifier.scaledMollifier_value

variable {d : ℕ} [NeZero d]

lemma rawBump_eq_glue (x : Point d) :
    rawBump d x = expNegInvGlue (1 - ‖x‖ ^ 2) := by
  by_cases hx : ‖x‖ < 1
  · have h : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    simp [rawBump, Specs.D11.Ch11.SmoothMollifier.rawBump_value, hx,
      expNegInvGlue, not_le.mpr h, div_eq_mul_inv]
  · have h : 1 - ‖x‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg x, le_of_not_gt hx]
    simp [rawBump, Specs.D11.Ch11.SmoothMollifier.rawBump_value, hx,
      expNegInvGlue.zero_of_nonpos h]

lemma rawBump_smooth : ContDiff ℝ ∞ (rawBump d) := by
  have h : ContDiff ℝ ∞ (fun x : Point d => expNegInvGlue (1 - ‖x‖ ^ 2)) :=
    expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_norm_sq ℝ))
  simpa only [← rawBump_eq_glue] using h

lemma rawBump_nonneg (x : Point d) : 0 ≤ rawBump d x := by
  rw [rawBump_eq_glue]
  exact expNegInvGlue.nonneg _

lemma rawBump_support : tsupport (rawBump d) ⊆ Metric.closedBall 0 1 := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have h : ‖x‖ < 1 := by
    by_contra h
    exact hx (by simp [rawBump, Specs.D11.Ch11.SmoothMollifier.rawBump_value, h])
  simpa only [Metric.mem_closedBall, dist_zero_right] using h.le

lemma rawBump_compact : HasCompactSupport (rawBump d) :=
  (isCompact_closedBall (0 : Point d) 1).of_isClosed_subset (isClosed_tsupport _) rawBump_support

lemma rawBump_integrable_borel : Integrable (rawBump d) volume :=
  rawBump_smooth.continuous.integrable_of_hasCompactSupport rawBump_compact

lemma rawBump_integral_borel_pos : 0 < ∫ x, rawBump d x ∂volume := by
  apply rawBump_smooth.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    rawBump_compact rawBump_nonneg (x := 0)
  rw [rawBump_eq_glue]
  exact (expNegInvGlue.pos_of_pos (by simp)).ne'

lemma integral_completed_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Point d → F) (hf : StronglyMeasurable f) :
    (∫ x, f x ∂lebesgue_value d) = ∫ x, f x ∂volume := by
  have H := integral_trim (μ := lebesgue_value d) (native_borel_le d) hf
  rwa [borel_restriction d (native_borel_le d)] at H

lemma integrable_completed {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Point d → F) (_hf : StronglyMeasurable f) (hi : Integrable f volume) :
    letI := lebesgueSpace_value d; Integrable f (lebesgue_value d) := by
  exact integrable_of_integrable_trim (native_borel_le d)
    ((borel_restriction d (native_borel_le d)).symm ▸ hi)

lemma rawBump_integral_pos : 0 < ∫ x, rawBump d x ∂lebesgue_value d := by
  rw [integral_completed_eq _ rawBump_smooth.continuous.stronglyMeasurable]
  exact rawBump_integral_borel_pos

theorem rawBump_properties : Specs.D11.Ch11.SmoothMollifier.rawBump_properties := by
  intro d _
  exact ⟨rawBump_smooth, rawBump_nonneg, rawBump_support, rawBump_compact,
    integrable_completed _ rawBump_smooth.continuous.stronglyMeasurable
      rawBump_integrable_borel, rawBump_integral_pos⟩

lemma mollifier_smooth : ContDiff ℝ ∞ (mollifier d) :=
  contDiff_const.mul rawBump_smooth

lemma mollifier_nonneg (x : Point d) : 0 ≤ mollifier d x :=
  mul_nonneg (inv_nonneg.mpr rawBump_integral_pos.le) (rawBump_nonneg x)

lemma mollifier_support : tsupport (mollifier d) ⊆ Metric.closedBall 0 1 := by
  exact tsupport_mul_subset_right.trans rawBump_support

lemma mollifier_compact : HasCompactSupport (mollifier d) :=
  (isCompact_closedBall (0 : Point d) 1).of_isClosed_subset (isClosed_tsupport _) mollifier_support

theorem mollifier_properties : Specs.D11.Ch11.SmoothMollifier.mollifier_properties := by
  intro d _
  refine ⟨mollifier_smooth, mollifier_nonneg, mollifier_support, mollifier_compact, ?_, ?_⟩
  · exact integrable_completed _ mollifier_smooth.continuous.stronglyMeasurable
      (mollifier_smooth.continuous.integrable_of_hasCompactSupport mollifier_compact)
  · change (∫ x, (∫ y, rawBump d y ∂lebesgue_value d)⁻¹ * rawBump d x
        ∂lebesgue_value d) = 1
    rw [integral_const_mul, inv_mul_cancel₀ rawBump_integral_pos.ne']

lemma scaledMollifier_smooth (t : ℝ) : ContDiff ℝ ∞ (scaledMollifier d t) :=
  contDiff_const.mul (mollifier_smooth.comp ((contDiff_id : ContDiff ℝ ∞ (fun x : Point d => x)).const_smul t⁻¹))

lemma scaledMollifier_nonneg {t : ℝ} (ht : 0 < t) (x : Point d) :
    0 ≤ scaledMollifier d t x :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg ht.le _)) (mollifier_nonneg _)

lemma scaledMollifier_support {t : ℝ} (ht : 0 < t) :
    tsupport (scaledMollifier d t) ⊆ Metric.closedBall 0 t := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have hm : mollifier d (t⁻¹ • x) ≠ 0 := by
    intro h
    apply hx
    simp [scaledMollifier, Specs.D11.Ch11.SmoothMollifier.scaledMollifier_value, h]
  have hn := mollifier_support (subset_closure hm)
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_pos ht] at hn
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [inv_mul_cancel₀ ht.ne']

lemma scaledMollifier_compact {t : ℝ} (ht : 0 < t) :
    HasCompactSupport (scaledMollifier d t) :=
  (isCompact_closedBall (0 : Point d) t).of_isClosed_subset
    (isClosed_tsupport _) (scaledMollifier_support ht)

theorem scaledMollifier_properties :
    Specs.D11.Ch11.SmoothMollifier.scaledMollifier_properties := by
  intro d _ t ht
  exact ⟨scaledMollifier_smooth t, scaledMollifier_nonneg ht,
    scaledMollifier_support ht, scaledMollifier_compact ht⟩

section Convolution
variable {𝕜 : Type} [RCLike 𝕜] {g k : Point d → 𝕜}
open Specs.D11.Ch11.ConvolutionBound (convolution_value)

/-- The ordinary convolution formula is unchanged on passing from the Borel
restriction to its completion; this uses measurability, not equality of spaces. -/
lemma convolution_eq_native (hg : Continuous g) (hk : Continuous k) :
    convolution_value d g k =
      MeasureTheory.convolution g k (ContinuousLinearMap.mul ℝ 𝕜) volume := by
  funext x
  exact integral_completed_eq _ (hg.mul (hk.comp (continuous_const.sub continuous_id))).stronglyMeasurable

lemma convolution_smooth (hg : Continuous g) (hk : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k) : ContDiff ℝ ∞ (convolution_value d g k) := by
  rw [convolution_eq_native hg hk.continuous]
  exact hkc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ 𝕜) hg.locallyIntegrable hk

lemma convolution_compact (hg : Continuous g) (hgc : HasCompactSupport g)
    (hk : Continuous k) (hkc : HasCompactSupport k) :
    HasCompactSupport (convolution_value d g k) := by
  rw [convolution_eq_native hg hk]
  exact hgc.convolution (ContinuousLinearMap.mul ℝ 𝕜) hkc

lemma convolution_integrable (hg : Continuous g) (hk : Continuous k)
    (hkc : HasCompactSupport k) (x : Point d) :
    letI := lebesgueSpace_value d;
    Integrable (fun y => g y * k (x-y)) (lebesgue_value d) := by
  exact integrable_completed _
    (hg.mul (hk.comp (continuous_const.sub continuous_id))).stronglyMeasurable
    (hkc.convolutionExists_right (ContinuousLinearMap.mul ℝ 𝕜) hg.locallyIntegrable hk x)

lemma convolution_derivative_integrable (hg : Continuous g) (hk : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k) (x : Point d) :
    letI := lebesgueSpace_value d;
    Integrable (fun y => (ContinuousLinearMap.mul ℝ 𝕜 (g y)).comp
      (fderiv ℝ k (x-y))) (lebesgue_value d) := by
  have hd : Continuous (fderiv ℝ k) := (hk.fderiv_right (m := 0) (by simp)).continuous
  have hm : Continuous (fun y => (ContinuousLinearMap.mul ℝ 𝕜 (g y)).comp
      (fderiv ℝ k (x-y))) := by fun_prop
  exact integrable_completed _ hm.stronglyMeasurable
    ((hkc.fderiv ℝ).convolutionExists_right
      ((ContinuousLinearMap.mul ℝ 𝕜).precompR (Point d)) hg.locallyIntegrable hd x)

lemma convolution_hasFDerivAt (hg : Continuous g) (hk : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k) (x : Point d) :
    HasFDerivAt (convolution_value d g k)
      (∫ y, (ContinuousLinearMap.mul ℝ 𝕜 (g y)).comp
        (fderiv ℝ k (x-y)) ∂lebesgue_value d) x := by
  have hd : Continuous (fderiv ℝ k) := (hk.fderiv_right (m := 0) (by simp)).continuous
  have hm : Continuous (fun y => (ContinuousLinearMap.mul ℝ 𝕜 (g y)).comp
      (fderiv ℝ k (x-y))) := by fun_prop
  rw [integral_completed_eq _ hm.stronglyMeasurable, convolution_eq_native hg hk.continuous]
  exact hkc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ 𝕜)
    hg.locallyIntegrable (hk.of_le (by simp)) x

open Specs.D11.Ch11.SmoothMollifier (iterDirectional)

omit [NeZero d] in
lemma iterDirectional_properties (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
    (vs : List (Point d)) :
    ContDiff ℝ ∞ (iterDirectional vs k) ∧ HasCompactSupport (iterDirectional vs k) := by
  induction vs with
  | nil => exact ⟨hk, hkc⟩
  | cons v vs ih =>
    exact ⟨(ih.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const,
      ih.2.fderiv_apply ℝ v⟩

lemma convolution_directional (hg : Continuous g) (hk : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k) (v : Point d) :
    (fun x => fderiv ℝ (convolution_value d g k) x v) =
      convolution_value d g (fun x => fderiv ℝ k x v) := by
  have hd : Continuous (fderiv ℝ k) := (hk.fderiv_right (m := 0) (by simp)).continuous
  have hdv : Continuous (fun x => fderiv ℝ k x v) := hd.clm_apply continuous_const
  rw [convolution_eq_native hg hk.continuous, convolution_eq_native hg hdv]
  funext x
  rw [(hkc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ 𝕜)
    hg.locallyIntegrable (hk.of_le (by simp)) x).fderiv]
  exact MeasureTheory.convolution_precompR_apply (ContinuousLinearMap.mul ℝ 𝕜)
    hg.locallyIntegrable (hkc.fderiv ℝ) hd x v

lemma convolution_iterDirectional (hg : Continuous g) (hk : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k) (vs : List (Point d)) :
    iterDirectional vs (convolution_value d g k) =
      convolution_value d g (iterDirectional vs k) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    dsimp only [iterDirectional]
    rw [ih]
    exact convolution_directional hg (iterDirectional_properties hk hkc vs).1
      (iterDirectional_properties hk hkc vs).2 v

end Convolution

set_option maxHeartbeats 800000 in
theorem regularization : Specs.D11.Ch11.SmoothMollifier.regularization := by
  intro d _ 𝕜 _ g hg hgc t ht
  let k : Point d → 𝕜 := fun x => (scaledMollifier d t x : 𝕜)
  have hk : ContDiff ℝ ∞ k := by
    simpa only [Function.comp_def, RCLike.ofRealCLM_apply] using
      (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp (scaledMollifier_smooth (d := d) t)
  have hkc : HasCompactSupport k :=
    (scaledMollifier_compact (d := d) ht).comp_left
      (g := fun r : ℝ => (r : 𝕜)) (by simp)
  exact ⟨convolution_smooth (d := d) (g := g) (k := k) hg hk hkc, convolution_compact (d := d) (g := g) (k := k) hg hgc hk.continuous hkc,
    convolution_integrable (d := d) (g := g) (k := k) hg hk.continuous hkc,
    convolution_derivative_integrable (d := d) (g := g) (k := k) hg hk hkc, convolution_hasFDerivAt (d := d) (g := g) (k := k) hg hk hkc⟩

set_option maxHeartbeats 800000 in
theorem regularization_all_derivatives :
    Specs.D11.Ch11.SmoothMollifier.regularization_all_derivatives := by
  intro d _ 𝕜 _ g hg hgc t ht
  let k : Point d → 𝕜 := fun x => (scaledMollifier d t x : 𝕜)
  have hk : ContDiff ℝ ∞ k := by
    simpa only [Function.comp_def, RCLike.ofRealCLM_apply] using
      (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp (scaledMollifier_smooth (d := d) t)
  have hkc : HasCompactSupport k :=
    (scaledMollifier_compact (d := d) ht).comp_left
      (g := fun r : ℝ => (r : 𝕜)) (by simp)
  dsimp only
  intro vs
  exact ⟨convolution_iterDirectional (d := d) (g := g) (k := k) hg hk hkc vs,
    convolution_integrable (d := d) (g := g)
      (k := Specs.D11.Ch11.SmoothMollifier.iterDirectional vs k) hg
      (iterDirectional_properties hk hkc vs).1.continuous
      (iterDirectional_properties hk hkc vs).2⟩

end D11.Ch11.SmoothMollifier
