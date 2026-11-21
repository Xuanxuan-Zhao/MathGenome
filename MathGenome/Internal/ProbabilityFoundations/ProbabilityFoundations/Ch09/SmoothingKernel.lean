import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch09.SmoothingKernel
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
A fixed smoothing kernel for paper.tex:3250–3267. Choose a smooth real even
frequency bump b supported in |ξ| < 1/(4π), with b(0)=1. Its Fourier transform
g is real and even. The function g² is a nonzero nonnegative Schwartz function;
normalize its integral to obtain J. Fourier inversion identifies the Fourier
transform of g² with (b ⋆ b)(-ξ), supported in |ξ| ≤ 1/(2π). The probability
frequency ξ=-t/(2π) therefore gives the required cutoff |t|≤1. Schwartz decay
supplies both integrability and the first absolute moment. This alternative
witness avoids the manuscript's auxiliary four-uniform density q.
-/

open MeasureTheory Filter Topology
open scoped FourierTransform SchwartzMap ComplexConjugate Convolution

namespace ProbabilityFoundations.Ch09

private noncomputable def frequencyBump : ContDiffBump (0 : ℝ) where
  rIn := (8 * Real.pi)⁻¹
  rOut := (4 * Real.pi)⁻¹
  rIn_pos := by positivity
  rIn_lt_rOut := by exact (inv_lt_inv₀ (by positivity) (by positivity)).2 (by nlinarith [Real.pi_pos])

private noncomputable def bump : 𝓢(ℝ, ℂ) :=
  (frequencyBump.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp frequencyBump.contDiff)

private lemma bump_apply (x : ℝ) : bump x = (frequencyBump x : ℂ) := rfl

private lemma bump_even (x : ℝ) : bump (-x) = bump x := by
  simp only [bump_apply, frequencyBump.neg]

private lemma bump_zero (x : ℝ) (hx : (4 * Real.pi)⁻¹ ≤ |x|) : bump x = 0 := by
  rw [bump_apply, frequencyBump.zero_of_le_dist]
  · simp
  · simpa [frequencyBump, Real.dist_eq] using hx

private lemma transform_even (x : ℝ) : (𝓕 bump) (-x) = (𝓕 bump) x := by
  rw [SchwartzMap.fourier_coe]
  have h := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) (bump : ℝ → ℂ) x
  change 𝓕 (fun y => bump (-y)) x = 𝓕 (bump : ℝ → ℂ) (-x) at h
  simpa only [bump_even] using h.symm

private lemma transform_real (x : ℝ) : ((𝓕 bump) x).im = 0 := by
  have hc : conj ((𝓕 bump) x) = (𝓕 bump) x := by
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul,
      ← integral_conj, ← integral_neg_eq_self]
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I, bump_apply, frequencyBump.neg, Complex.conj_ofReal]
    congr 2
    push_cast
    ring
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  linarith

private noncomputable def squareTransform : 𝓢(ℝ, ℂ) :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 bump) (𝓕 bump)

private noncomputable def rawKernel : 𝓢(ℝ, ℝ) :=
  squareTransform.postcompCLM Complex.reCLM

private lemma rawKernel_apply (x : ℝ) : rawKernel x = ((𝓕 bump) x).re ^ 2 := by
  change (((𝓕 bump) x) * ((𝓕 bump) x)).re = _
  simp [Complex.mul_re, transform_real, pow_two]

private lemma rawKernel_complex (x : ℝ) : (rawKernel x : ℂ) = squareTransform x := by
  apply Complex.ext
  · rfl
  · change 0 = (((𝓕 bump) x) * ((𝓕 bump) x)).im
    simp [Complex.mul_im, transform_real]

private lemma rawKernel_nonneg (x : ℝ) : 0 ≤ rawKernel x := by
  rw [rawKernel_apply]
  positivity

private lemma rawKernel_even (x : ℝ) : rawKernel (-x) = rawKernel x := by
  simp only [rawKernel_apply, transform_even]

private lemma rawKernel_mass_pos : 0 < ∫ x : ℝ, rawKernel x := by
  have hb : bump (0 : ℝ) = 1 := by
    rw [bump_apply, frequencyBump.one_of_mem_closedBall]
    · simp
    · exact Metric.mem_closedBall_self frequencyBump.rIn_pos.le
  have hn : ∃ x : ℝ, (𝓕 bump) x ≠ 0 := by
    by_contra h
    push Not at h
    have hz : 𝓕 bump = 0 := by ext x; exact h x
    have hbz : bump = 0 := by
      have := congrArg (fun f : 𝓢(ℝ, ℂ) => 𝓕⁻ f) hz
      simpa using this
    have := congrArg (fun f : 𝓢(ℝ, ℂ) => f 0) hbz
    simp [hb] at this
  obtain ⟨x, hx⟩ := hn
  apply integral_pos_of_integrable_nonneg_nonzero rawKernel.continuous rawKernel.integrable
    rawKernel_nonneg (x := x)
  rw [rawKernel_apply]
  apply pow_ne_zero
  intro hr
  apply hx
  exact Complex.ext hr (transform_real x)

private lemma squareTransform_fourier (w : ℝ) :
    𝓕 (squareTransform : ℝ → ℂ) w =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) bump bump (-w) := by
  let c := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) bump bump
  have h := congrArg (fun f : 𝓢(ℝ, ℂ) => f (-w)) (FourierTransform.fourierInv_fourier_eq (F := 𝓢(ℝ, ℂ)) c)
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_neg] at h
  simpa only [c, SchwartzMap.fourier_convolution, squareTransform] using h

private lemma squareTransform_cutoff (w : ℝ) (hw : 2 * (4 * Real.pi)⁻¹ < |w|) :
    𝓕 (squareTransform : ℝ → ℂ) w = 0 := by
  rw [squareTransform_fourier, SchwartzMap.convolution_apply, convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  change bump y * bump (-w - y) = 0
  by_cases hy : (4 * Real.pi)⁻¹ ≤ |y|
  · rw [bump_zero y hy, zero_mul]
  · have h : (4 * Real.pi)⁻¹ ≤ |-w - y| := by
      have ht := abs_add_le (-w - y) y
      simp only [sub_add_cancel, abs_neg] at ht
      linarith
    rw [bump_zero _ h, mul_zero]

/-- Conversion to the manuscript's plus-sign probability convention. -/
private lemma density_charFun_fourier (J : ℝ → ℝ) (hm : Measurable J)
    (hn : ∀ x, 0 ≤ J x) (t : ℝ) :
    charFun (volume.withDensity (fun x => ENNReal.ofReal (J x))) t =
      𝓕 (fun x => (J x : ℂ)) (-t / (2 * Real.pi)) := by
  rw [charFun, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)),
    Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ENNReal.toReal_ofReal (hn x), smul_eq_mul,
    RCLike.inner_apply, conj_trivial]
  have he : -2 * Real.pi * x * (-t / (2 * Real.pi)) = x * t := by
    field_simp
  rw [he]
  simp [Complex.real_smul, mul_comm]

private noncomputable def normalizedKernel : 𝓢(ℝ, ℝ) :=
  (∫ x : ℝ, rawKernel x)⁻¹ • rawKernel

private lemma normalizedKernel_apply (x : ℝ) :
    normalizedKernel x = (∫ y : ℝ, rawKernel y)⁻¹ * rawKernel x := rfl

private lemma normalizedKernel_nonneg (x : ℝ) : 0 ≤ normalizedKernel x := by
  rw [normalizedKernel_apply]
  exact mul_nonneg (inv_nonneg.mpr rawKernel_mass_pos.le) (rawKernel_nonneg x)

private lemma normalizedKernel_mass : (∫ x : ℝ, normalizedKernel x) = 1 := by
  simp only [normalizedKernel_apply, integral_const_mul]
  exact inv_mul_cancel₀ rawKernel_mass_pos.ne'

private lemma normalizedKernel_complex :
    (fun x : ℝ => (normalizedKernel x : ℂ)) =
      ((∫ y : ℝ, rawKernel y : ℝ) : ℂ)⁻¹ • (squareTransform : ℝ → ℂ) := by
  ext x
  simp only [normalizedKernel_apply, Complex.ofReal_mul, Complex.ofReal_inv,
    Pi.smul_apply, smul_eq_mul, rawKernel_complex]

private lemma normalizedKernel_charFun_cutoff (t : ℝ) (ht : 1 < |t|) :
    charFun (volume.withDensity (fun x => ENNReal.ofReal (normalizedKernel x))) t = 0 := by
  rw [density_charFun_fourier normalizedKernel normalizedKernel.continuous.measurable
    normalizedKernel_nonneg, normalizedKernel_complex]
  change (𝓕 ((((∫ y : ℝ, rawKernel y : ℝ) : ℂ)⁻¹ • squareTransform) : 𝓢(ℝ, ℂ)))
    (-t / (2 * Real.pi)) = 0
  rw [FourierTransform.fourier_smul]
  change _ * 𝓕 (squareTransform : ℝ → ℂ) (-t / (2 * Real.pi)) = 0
  rw [squareTransform_cutoff, mul_zero]
  rw [abs_div, abs_neg, abs_of_pos (show 0 < 2 * Real.pi by positivity)]
  apply (lt_div_iff₀ (by positivity)).2
  have he : 2 * (4 * Real.pi)⁻¹ * (2 * Real.pi) = 1 := by
    field_simp
    ring
  rwa [he]

private lemma normalizedKernel_charFun_continuous :
    Continuous (charFun (volume.withDensity (fun x => ENNReal.ofReal (normalizedKernel x)))) := by
  have he : charFun (volume.withDensity (fun x => ENNReal.ofReal (normalizedKernel x))) =
      fun t : ℝ =>
        𝓕 (((∫ y : ℝ, rawKernel y : ℝ) : ℂ)⁻¹ • squareTransform) (-t / (2 * Real.pi)) := by
    ext t
    rw [density_charFun_fourier normalizedKernel normalizedKernel.continuous.measurable
      normalizedKernel_nonneg, normalizedKernel_complex]
    rfl
  rw [he]
  exact (SchwartzMap.continuous _).comp (by fun_prop)

/-- A fixed numerical smoothing kernel, chosen before all laws and smoothing
scales. Its construction uses a smooth compactly supported frequency bump,
rather than the sinc fourth-power witness of the manuscript. -/
theorem exists_smoothingKernel :
    Specs.ProbabilityFoundations.Ch09.SmoothingKernel.ExistsSmoothingKernel := by
  have hp : IsProbabilityMeasure
      (volume.withDensity (fun x => ENNReal.ofReal (normalizedKernel x))) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal normalizedKernel.integrable
        (ae_of_all _ normalizedKernel_nonneg), normalizedKernel_mass]
    norm_num
  haveI := hp
  refine ⟨normalizedKernel, normalizedKernel.continuous, ?_, normalizedKernel_nonneg,
    ?_, normalizedKernel.integrable, normalizedKernel_mass, ?_, hp,
    normalizedKernel_charFun_cutoff, (fun t => norm_charFun_le_one t),
    normalizedKernel_charFun_continuous, ?_⟩
  · intro x
    simp only [normalizedKernel_apply, rawKernel_even]
  · refine ⟨SchwartzMap.seminorm ℝ 0 0 normalizedKernel, fun x => ?_⟩
    simpa only [Real.norm_eq_abs] using SchwartzMap.norm_le_seminorm ℝ normalizedKernel x
  · convert normalizedKernel.integrable_pow_mul volume 1 using 1
    ext x
    simp only [pow_one, Real.norm_eq_abs, abs_of_nonneg (normalizedKernel_nonneg x)]
  · apply normalizedKernel_charFun_continuous.integrable_of_hasCompactSupport
    apply HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc
    intro t ht
    apply normalizedKernel_charFun_cutoff
    exact lt_of_not_ge (fun h => ht (abs_le.mp h))

end ProbabilityFoundations.Ch09
