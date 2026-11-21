import MathGenome.Internal.FourierSobolev.Specs.P102.U3.FiniteMeasureFourier
import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FunProp

noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped RealInnerProductSpace

namespace P102.U3.FiniteMeasureFourier
open P102.Specs.U3 (Euclidean)

abbrev kernel := @P102.Specs.U3.FiniteMeasureFourier.kernelValue
abbrev signedTransform := @P102.Specs.U3.FiniteMeasureFourier.signedTransformValue
abbrev complexTransform := @P102.Specs.U3.FiniteMeasureFourier.complexTransformValue

lemma norm_kernel {d : ℕ} (ξ x : Euclidean d) : ‖kernel ξ x‖ = 1 := by
  simp only [kernel, P102.Specs.U3.FiniteMeasureFourier.kernelValue, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
    mul_zero, zero_mul, sub_zero, Real.exp_zero]

lemma continuous_kernel {d : ℕ} (ξ : Euclidean d) : Continuous (kernel ξ) := by
  unfold kernel P102.Specs.U3.FiniteMeasureFourier.kernelValue
  fun_prop

lemma continuous_kernel_frequency {d : ℕ} (x : Euclidean d) :
    Continuous (fun ξ => kernel ξ x) := by
  unfold kernel P102.Specs.U3.FiniteMeasureFourier.kernelValue
  fun_prop

lemma integrable_kernel {d : ℕ} (ξ : Euclidean d) (μ : Measure (Euclidean d))
    [IsFiniteMeasure μ] : Integrable (kernel ξ) μ := by
  exact (integrable_const (1 : ℝ)).mono
    (continuous_kernel ξ).aestronglyMeasurable (by simp [norm_kernel])

lemma finite_signed_variation {X : Type*} [MeasurableSpace X] (ν : SignedMeasure X) :
    IsFiniteMeasure ν.variation := by
  rw [← ν.totalVariation_eq_variation]
  infer_instance

lemma norm_mul_pair : ‖ContinuousLinearMap.mul ℝ ℂ‖ = 1 := by
  exact ContinuousLinearMap.opNorm_mul ℝ ℂ

lemma norm_signed_pair : ‖(ContinuousLinearMap.lsmul ℝ ℝ :
    ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip‖ = 1 := by
  rw [ContinuousLinearMap.opNorm_flip]
  exact ContinuousLinearMap.opNorm_lsmul ℝ ℝ

theorem signed_bound : P102.Specs.U3.FiniteMeasureFourier.signedBoundStatement := by
  intro d ν ξ
  let := finite_signed_variation ν
  have h := VectorMeasure.norm_integral_le_of_norm_le_const
    (μ := ν) (B := (lsmul ℝ ℝ).flip) (f := kernel ξ) (C := 1)
    (Filter.Eventually.of_forall fun x => (norm_kernel ξ x).le)
  simpa [signedTransform, P102.Specs.U3.FiniteMeasureFourier.signedTransformValue,
    norm_signed_pair, ← ν.totalVariation_eq_variation] using h

theorem complex_bound : P102.Specs.U3.FiniteMeasureFourier.complexBoundStatement := by
  intro d ν hν ξ
  have h := VectorMeasure.norm_integral_le_of_norm_le_const
    (μ := ν) (B := mul ℝ ℂ) (f := kernel ξ) (C := 1)
    (Filter.Eventually.of_forall fun x => (norm_kernel ξ x).le)
  simpa [complexTransform, P102.Specs.U3.FiniteMeasureFourier.complexTransformValue,
    norm_mul_pair] using h

theorem signed_continuous : P102.Specs.U3.FiniteMeasureFourier.signedContinuousStatement := by
  intro d ν
  let := finite_signed_variation ν
  exact VectorMeasure.continuous_of_dominated
    (fun ξ => (continuous_kernel ξ).aestronglyMeasurable)
    (fun ξ => Filter.Eventually.of_forall fun x => (norm_kernel ξ x).le)
    (integrable_const (1 : ℝ))
    (Filter.Eventually.of_forall continuous_kernel_frequency)

theorem complex_continuous : P102.Specs.U3.FiniteMeasureFourier.complexContinuousStatement := by
  intro d ν hν
  exact VectorMeasure.continuous_of_dominated
    (fun ξ => (continuous_kernel ξ).aestronglyMeasurable)
    (fun ξ => Filter.Eventually.of_forall fun x => (norm_kernel ξ x).le)
    (integrable_const (1 : ℝ))
    (Filter.Eventually.of_forall continuous_kernel_frequency)

/-- The ordinary integral with respect to a positive measure. -/
def positiveTransform {d : ℕ} (μ : Measure (Euclidean d)) (ξ : Euclidean d) : ℂ :=
  ∫ x, kernel ξ x ∂μ

lemma positiveTransform_charFun {d : ℕ} (μ : Measure (Euclidean d)) (ξ : Euclidean d) :
    positiveTransform μ ξ = charFun μ ((-2 * Real.pi) • ξ) := by
  simp only [positiveTransform, kernel, P102.Specs.U3.FiniteMeasureFourier.kernelValue,
    charFun_apply, inner_smul_right]

lemma positive_ext {d : ℕ} (μ η : Measure (Euclidean d))
    [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (h : ∀ ξ, positiveTransform μ ξ = positiveTransform η ξ) : μ = η := by
  apply Measure.ext_of_charFun
  ext t
  have hπ : -2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  simpa only [positiveTransform_charFun, smul_smul, mul_inv_cancel₀ hπ, one_smul]
    using h ((-2 * Real.pi)⁻¹ • t)

lemma signedTransform_jordan {d : ℕ} (ν : SignedMeasure (Euclidean d)) (ξ : Euclidean d) :
    signedTransform ν ξ = positiveTransform ν.toJordanDecomposition.posPart ξ -
      positiveTransform ν.toJordanDecomposition.negPart ξ := by
  change (∫ᵛ x, kernel ξ x ∂<•ν) = _
  conv_lhs => rw [← ν.toSignedMeasure_toJordanDecomposition]
  rw [JordanDecomposition.toSignedMeasure, VectorMeasure.integral_sub_vectorMeasure]
  · simp only [VectorMeasure.integral_toSignedMeasure, positiveTransform]
  all_goals
    change Integrable (kernel ξ) _
    simpa only [Measure.variation_toSignedMeasure] using integrable_kernel ξ _

lemma signedTransform_neg {d : ℕ} (ν : SignedMeasure (Euclidean d)) (ξ : Euclidean d) :
    signedTransform ν (-ξ) = starRingEnd ℂ (signedTransform ν ξ) := by
  simp only [signedTransform_jordan, positiveTransform_charFun, smul_neg, charFun_neg,
    map_sub]

theorem signed_injective : P102.Specs.U3.FiniteMeasureFourier.signedInjectiveStatement := by
  intro d ν η h
  have heq : ν.toJordanDecomposition.posPart + η.toJordanDecomposition.negPart =
      η.toJordanDecomposition.posPart + ν.toJordanDecomposition.negPart := by
    apply positive_ext
    intro ξ
    have hh := h ξ
    change signedTransform ν ξ = signedTransform η ξ at hh
    rw [signedTransform_jordan, signedTransform_jordan] at hh
    simp only [positiveTransform, integral_add_measure (integrable_kernel ξ _)
      (integrable_kernel ξ _)]
    change positiveTransform ν.toJordanDecomposition.posPart ξ +
      positiveTransform η.toJordanDecomposition.negPart ξ =
      positiveTransform η.toJordanDecomposition.posPart ξ +
      positiveTransform ν.toJordanDecomposition.negPart ξ
    linear_combination hh
  have heq' :
      (ν.toJordanDecomposition.posPart + η.toJordanDecomposition.negPart).toSignedMeasure =
      (η.toJordanDecomposition.posPart + ν.toJordanDecomposition.negPart).toSignedMeasure := by
    ext s hs
    simpa only [Measure.toSignedMeasure_apply_measurable hs]
      using congrArg (fun μ : Measure (Euclidean d) => μ.real s) heq
  simp only [Measure.toSignedMeasure_add] at heq'
  have hs : ν.toJordanDecomposition.toSignedMeasure =
      η.toJordanDecomposition.toSignedMeasure := by
    simp only [JordanDecomposition.toSignedMeasure]
    exact sub_eq_sub_iff_add_eq_add.mpr heq'
  simpa only [SignedMeasure.toSignedMeasure_toJordanDecomposition] using hs

/-- Pair a complex integrand with the real part of a complex measure. -/
def realPair : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ((lsmul ℝ ℝ).comp Complex.reCLM).flip
/-- Pair a complex integrand with the imaginary part of a complex measure. -/
def imagPair : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ((lsmul ℝ ℝ).comp Complex.imCLM).flip

lemma integral_realPart {d : ℕ} (ν : ComplexMeasure (Euclidean d))
    [IsFiniteMeasure ν.variation] (ξ : Euclidean d) :
    signedTransform ν.re ξ = ∫ᵛ x, kernel ξ x ∂[realPair; ν] := by
  let := finite_signed_variation ν.re
  change (∫ᵛ x, kernel ξ x ∂<•ν.re) = _
  rw [VectorMeasure.integral_eq_setToFun_transpose (integrable_kernel ξ _),
    VectorMeasure.integral_eq_setToFun_transpose (integrable_kernel ξ _)]
  have ht : ν.re.transpose (lsmul ℝ ℝ).flip = ν.transpose realPair := by
    ext s hs z
    rfl
  simp only [ht]

lemma integral_imagPart {d : ℕ} (ν : ComplexMeasure (Euclidean d))
    [IsFiniteMeasure ν.variation] (ξ : Euclidean d) :
    signedTransform ν.im ξ = ∫ᵛ x, kernel ξ x ∂[imagPair; ν] := by
  let := finite_signed_variation ν.im
  change (∫ᵛ x, kernel ξ x ∂<•ν.im) = _
  rw [VectorMeasure.integral_eq_setToFun_transpose (integrable_kernel ξ _),
    VectorMeasure.integral_eq_setToFun_transpose (integrable_kernel ξ _)]
  have ht : ν.im.transpose (lsmul ℝ ℝ).flip = ν.transpose imagPair := by
    ext s hs z
    rfl
  simp only [ht]

lemma mul_pair_decomposition :
    mul ℝ ℂ = realPair + (compL ℝ ℂ ℂ ℂ (mul ℝ ℂ Complex.I)).comp imagPair := by
  ext z w
  change z * w = (w.re : ℂ) * z + Complex.I * ((w.im : ℂ) * z)
  conv_lhs => rw [← Complex.re_add_im w]
  ring

/-- The actual complex vector integral agrees with integration against the
real and imaginary signed measures. -/
lemma complexTransform_parts {d : ℕ} (ν : ComplexMeasure (Euclidean d))
    [IsFiniteMeasure ν.variation] (ξ : Euclidean d) :
    complexTransform ν ξ = signedTransform ν.re ξ + Complex.I * signedTransform ν.im ξ := by
  rw [integral_realPart, integral_imagPart]
  change (∫ᵛ x, kernel ξ x ∂[mul ℝ ℂ; ν]) = _
  rw [mul_pair_decomposition, VectorMeasure.integral_add_cbm (integrable_kernel ξ _)]
  rw [← VectorMeasure.continuousLinearMap_apply_integral (integrable_kernel ξ _)]
  rfl

theorem complex_injective : P102.Specs.U3.FiniteMeasureFourier.complexInjectiveStatement := by
  intro d ν η hν hη h
  have hparts (ξ : Euclidean d) :
      signedTransform ν.re ξ + Complex.I * signedTransform ν.im ξ =
      signedTransform η.re ξ + Complex.I * signedTransform η.im ξ := by
    simpa only [← complexTransform_parts] using h ξ
  have hconj (ξ : Euclidean d) :
      signedTransform ν.re ξ - Complex.I * signedTransform ν.im ξ =
      signedTransform η.re ξ - Complex.I * signedTransform η.im ξ := by
    have hh := congrArg (starRingEnd ℂ) (hparts (-ξ))
    simpa only [signedTransform_neg, map_add, map_mul, starRingEnd_self_apply,
      Complex.conj_I, neg_mul, ← sub_eq_add_neg] using hh
  have hre : ν.re = η.re := by
    apply signed_injective
    intro ξ
    linear_combination (hparts ξ) / 2 + (hconj ξ) / 2
  have him : ν.im = η.im := by
    apply signed_injective
    intro ξ
    linear_combination (norm := (ring_nf; simp [Complex.I_sq]))
      -(Complex.I / 2) * (hparts ξ) + (Complex.I / 2) * (hconj ξ)
  exact ComplexMeasure.equivSignedMeasure.injective (Prod.ext hre him)

end P102.U3.FiniteMeasureFourier
