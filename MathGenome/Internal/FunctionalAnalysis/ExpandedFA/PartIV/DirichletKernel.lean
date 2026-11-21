import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.DirichletKernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory Filter
open scoped Real ENNReal Topology

namespace ExpandedFA.PartIV.DirichletKernel
open DirichletKernelSpec
abbrev Circle := DirichletKernelSpec.Circle

/-- Reindexing the symmetric integer interval by its 2N+1 consecutive terms. -/
theorem sum_frequencies {A : Type*} [AddCommMonoid A] (N : ℕ) (f : ℤ → A) :
    ∑ n ∈ frequencies N, f n = ∑ j ∈ Finset.range (2 * N + 1), f (-(N : ℤ) + j) := by
  unfold frequencies
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  have h : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
  rw [h]
  rfl

theorem kernel_exponential : KernelExponential := by
  intro N t
  simp only [kernel, ContinuousMap.sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp

theorem kernel_at_zero : KernelAtZero := by
  intro N
  simp only [kernel, ContinuousMap.sum_apply, fourier_eval_zero]
  rw [sum_frequencies]
  simp

theorem kernel_bound : KernelBound := by
  intro N x
  simp only [kernel, ContinuousMap.sum_apply]
  calc
    _ ≤ ∑ n ∈ frequencies N, ‖fourier n x‖ := norm_sum_le _ _
    _ = (2 * N + 1 : ℝ) := by
      rw [sum_frequencies]
      simp only [fourier_apply, Circle.norm_coe, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one]
      push_cast
      ring

/-- A sine identity without division, valid even at the removable singularities. -/
theorem kernel_sine_product (N : ℕ) (t : ℝ) :
    (Real.sin (t / 2) : ℂ) * kernel N (t : Circle) =
      (Real.sin (((N : ℝ) + 1 / 2) * t) : ℂ) := by
  rw [kernel_exponential, sum_frequencies]
  have he (j : ℕ) :
      Complex.exp (Complex.I * ((-(N : ℤ) + j : ℤ) : ℂ) * t) =
        (Real.cos (t * j - N * t) : ℂ) + (Real.sin (t * j - N * t) : ℂ) * Complex.I := by
    rw [show Complex.I * ((-(N : ℤ) + j : ℤ) : ℂ) * t =
      ((t * j - N * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
    simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
      Complex.exp_mul_I ((t * j - N * t : ℝ) : ℂ)
  simp_rw [he, Finset.sum_add_distrib, ← Finset.sum_mul, ← Complex.ofReal_sum]
  have hc := Real.sin_mul_sum_cos (2 * N + 1) t (-(N : ℝ) * t)
  have hs := Real.sin_mul_sum_sin (2 * N + 1) t (-(N : ℝ) * t)
  have ha : (((2 * N + 1 : ℕ) : ℝ) - 1) * t / 2 + -(N : ℝ) * t = 0 := by
    push_cast; ring
  have hb : ((2 * N + 1 : ℕ) : ℝ) * t / 2 = ((N : ℝ) + 1 / 2) * t := by
    push_cast; ring
  rw [ha, hb, Real.cos_zero, mul_one] at hc
  rw [ha, hb, Real.sin_zero, mul_zero] at hs
  rw [mul_add, ← mul_assoc, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  simp only [sub_eq_add_neg, neg_mul] at hc hs ⊢
  rw [hc, hs]
  simp

theorem kernel_quotient : KernelQuotient := by
  intro N t ht
  have h := kernel_sine_product N t
  rw [Complex.ofReal_div]
  apply (eq_div_iff (by exact_mod_cast ht : (Real.sin (t / 2) : ℂ) ≠ 0)).2
  simpa only [Complex.ofReal_div, mul_comm] using h

theorem fourier_sub (n : ℤ) (x t : Circle) :
    fourier n (x - t) = fourier n x * fourier (-n) t := by
  simp only [fourier_apply, sub_eq_add_neg, zsmul_add, zsmul_neg, AddCircle.toCircle_add,
    neg_zsmul, AddCircle.toCircle_neg, _root_.Circle.coe_mul,
    _root_.Circle.coe_inv_eq_conj]

/-- Finite Fourier synthesis agrees pointwise with convolution, without any
pointwise representative assumptions on the integrable input. -/
theorem convolution_identity : ConvolutionIdentity := by
  intro N f hf x
  unfold partialSum DirichletKernelSpec.convolution
  simp only [kernel, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
    Finset.sum_mul, fourier_sub, mul_assoc]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [integral_const_mul]
    simp only [fourierCoeff, smul_eq_mul, mul_comm]
  · intro n hn
    exact (hf.fourier_smul (-n)).const_mul (fourier n x)

theorem partialSumL1_representative (N : ℕ) (f : DirichletKernelSpec.L1) :
    (partialSumL1 N f : Circle → ℂ) =ᵐ[haar] partialSum N f := by
  unfold partialSumL1
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  have h (n : ℤ) :
      ((fourierCoeff f n • fourierLp (T := 2 * π) 1 n : DirichletKernelSpec.L1) : Circle → ℂ) =ᵐ[haar]
        (fun t => fourierCoeff f n * fourier n t) := by
    simpa only [Pi.smul_apply, smul_eq_mul, Function.comp_def] using
      (Lp.coeFn_smul (fourierCoeff f n) (fourierLp (T := 2 * π) 1 n)).trans
        ((coeFn_fourierLp 1 n).fun_comp (fun z => fourierCoeff f n • z))
  filter_upwards [eventuallyEq_sum (s := frequencies N) (fun n _ => h n)] with t ht
  simpa only [partialSum, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
    Finset.sum_apply] using ht

theorem l1_representative : L1Representative := by
  intro N f
  exact (partialSumL1_representative N f).trans
    (Filter.EventuallyEq.of_eq (funext (convolution_identity N f (L1.integrable_coeFn f))))

theorem kernel_conj (N : ℕ) (x : Circle) : star (kernel N x) = kernel N x := by
  change (starRingEnd ℂ) (kernel N x) = kernel N x
  simp only [kernel, ContinuousMap.sum_apply, map_sum, ← fourier_neg]
  apply Finset.sum_bij (fun n _ => -n)
  · intro n hn
    simp only [frequencies, Finset.mem_Icc] at hn ⊢
    omega
  · intro n hn m hm heq
    exact neg_injective heq
  · intro n hn
    refine ⟨-n, ?_, neg_neg n⟩
    simp only [frequencies, Finset.mem_Icc] at hn ⊢
    omega
  · intro n hn
    rfl

theorem kernel_real : KernelReal := by
  intro N x
  have hi := congrArg Complex.im (kernel_conj N x)
  change -(kernel N x).im = (kernel N x).im at hi
  have hz : (kernel N x).im = 0 := by linarith
  apply Complex.ext
  · rfl
  · simpa using hz.symm

theorem real_fourier_convolution : RealFourierConvolution := by
  intro N f hf x
  rw [convolution_identity N (fun t => (f t : ℂ)) hf.ofReal]
  unfold DirichletKernelSpec.convolution
  simp_rw [← kernel_real N (x - _), ← Complex.ofReal_mul]
  exact integral_complex_ofReal.symm

theorem lebesgueConstant_nonneg (N : ℕ) : 0 ≤ lebesgueConstant N :=
  integral_nonneg fun _ => norm_nonneg _

theorem lebesgueConstant_le (N : ℕ) : lebesgueConstant N ≤ 2 * N + 1 := by
  calc
    _ ≤ ∫ _ : Circle, (2 * N + 1 : ℝ) ∂haar := by
      apply integral_mono
        ((kernel N).continuous.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (integrable_const _)
      exact kernel_bound N
    _ = _ := by simp

theorem kernel_fourierCoeff (N : ℕ) (k : ℤ) :
    fourierCoeff (kernel N) k = if k ∈ frequencies N then 1 else 0 := by
  have hi (n : ℤ) : Integrable (fourier (T := 2 * π) n) haar :=
    (fourier n).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := congrFun (fourierCoeff.sum (frequencies N) (fun n => (fourier n : Circle → ℂ))
    (fun n _ => hi n)) k
  simp only [fourierCoeff_fourier, Pi.single_apply, Finset.sum_apply] at h
  simpa [kernel, ContinuousMap.coe_sum, eq_comm] using h

theorem kernel_integral (N : ℕ) : ∫ t, kernel N t ∂haar = 1 := by
  have h := kernel_fourierCoeff N 0
  simpa [fourierCoeff, frequencies] using h

theorem one_le_lebesgueConstant (N : ℕ) : 1 ≤ lebesgueConstant N := by
  have h := norm_integral_le_integral_norm (μ := haar) (fun t => kernel N t)
  simpa only [kernel_integral, norm_one, lebesgueConstant] using h

theorem lebesgueConstant_zero : lebesgueConstant 0 = 1 := by
  simp [lebesgueConstant, kernel, frequencies]

/-- Final assembly of norm divergence needs only the lower logarithmic estimate. -/
theorem kernelNormDivergence_of_logarithmicBounds (h : LogarithmicBounds) :
    KernelNormDivergence := by
  obtain ⟨c, C, hc, hC, hb⟩ := h
  apply tendsto_atTop_mono (fun N => (hb N).1)
  exact Tendsto.const_mul_atTop hc
    (Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop))

section Scalar
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Integration against a continuous density, bilinear rather than sesquilinear. -/
def integralFunctional (k : C(Circle, 𝕜)) : C(Circle, 𝕜) →L[𝕜] 𝕜 := by
  let L : C(Circle, 𝕜) →ₗ[𝕜] 𝕜 :=
    { toFun := fun f => ∫ t, k t * f t ∂haar
      map_add' := by
        intro f g
        simp only [ContinuousMap.add_apply, mul_add]
        exact integral_add
          ((k.continuous.mul f.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          ((k.continuous.mul g.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := by
        intro c f
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        simp_rw [mul_left_comm (k _) c, integral_const_mul] }
  refine L.mkContinuous (∫ t, ‖k t‖ ∂haar) fun f => ?_
  change ‖∫ t, k t * f t ∂haar‖ ≤ _
  calc
    _ ≤ ∫ t, ‖k t‖ * ‖f‖ ∂haar := by
      apply norm_integral_le_of_norm_le
        ((k.continuous.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).mul_const ‖f‖)
      exact ae_of_all _ fun t => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm t) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

@[simp] theorem integralFunctional_apply (k f : C(Circle, 𝕜)) :
    integralFunctional k f = ∫ t, k t * f t ∂haar := rfl

/-- A continuous regularization of the conjugate phase. -/
def regularizedPhase (k : C(Circle, 𝕜)) (ε : ℝ) (hε : 0 < ε) : C(Circle, 𝕜) :=
  ⟨fun t => star (k t) / ((‖k t‖ + ε : ℝ) : 𝕜),
    Continuous.div (by fun_prop) (by fun_prop) (fun t => by
      exact_mod_cast (ne_of_gt (add_pos_of_nonneg_of_pos (norm_nonneg (k t)) hε)))⟩

theorem regularizedPhase_norm_le (k : C(Circle, 𝕜)) (ε : ℝ) (hε : 0 < ε) :
    ‖regularizedPhase k ε hε‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).2
  intro t
  change ‖star (k t) / ((‖k t‖ + ε : ℝ) : 𝕜)‖ ≤ 1
  rw [norm_div, norm_star, RCLike.norm_ofReal,
    abs_of_pos (add_pos_of_nonneg_of_pos (norm_nonneg (k t)) hε)]
  exact (div_le_one (add_pos_of_nonneg_of_pos (norm_nonneg (k t)) hε)).2 (by linarith)

theorem regularizedPhase_error (k : C(Circle, 𝕜)) (ε : ℝ) (hε : 0 < ε) (t : Circle) :
    ‖(‖k t‖ : 𝕜) - k t * regularizedPhase k ε hε t‖ ≤ ε := by
  have hd : 0 < ‖k t‖ + ε := add_pos_of_nonneg_of_pos (norm_nonneg _) hε
  change ‖(‖k t‖ : 𝕜) - k t * (star (k t) / ((‖k t‖ + ε : ℝ) : 𝕜))‖ ≤ ε
  rw [← mul_div_assoc, RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_div,
    ← RCLike.ofReal_sub, RCLike.norm_ofReal]
  have he : ‖k t‖ - ‖k t‖ ^ 2 / (‖k t‖ + ε) = ε * ‖k t‖ / (‖k t‖ + ε) := by
    field_simp; ring
  rw [he, abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ hd).2
  nlinarith [norm_nonneg (k t)]

/-- Exact dual norm for continuous densities, including densities with zeros. -/
theorem integralFunctional_norm (k : C(Circle, 𝕜)) :
    ‖integralFunctional k‖ = ∫ t, ‖k t‖ ∂haar := by
  have hk : Integrable (fun t => ‖k t‖) haar :=
    k.continuous.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply le_antisymm
  · unfold integralFunctional
    apply LinearMap.mkContinuous_norm_le
    exact integral_nonneg fun _ => norm_nonneg _
  · apply le_of_forall_pos_le_add
    intro ε hε
    let f := regularizedPhase k ε hε
    have he : ‖((∫ t, ‖k t‖ ∂haar : ℝ) : 𝕜) - integralFunctional k f‖ ≤ ε := by
      rw [integralFunctional_apply, ← integral_ofReal (𝕜 := 𝕜), ← integral_sub]
      · simpa using norm_integral_le_of_norm_le_const
          (ae_of_all haar (regularizedPhase_error k ε hε))
      · exact hk.ofReal
      · exact (k.continuous.mul f.continuous).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    have hf : ‖integralFunctional k f‖ ≤ ‖integralFunctional k‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) (regularizedPhase_norm_le k ε hε))
    have ht := norm_sub_norm_le
      (((∫ t, ‖k t‖ ∂haar : ℝ) : 𝕜)) (integralFunctional k f)
    rw [RCLike.norm_ofReal, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at ht
    linarith

end Scalar

def evaluation (N : ℕ) (x : Circle) : C(Circle, ℂ) →L[ℂ] ℂ :=
  integralFunctional ⟨fun t => kernel N (x - t), by fun_prop⟩

theorem evaluation_apply (N : ℕ) (x : Circle) (f : C(Circle, ℂ)) :
    evaluation N x f = partialSum N f x := by
  exact (convolution_identity N f
    (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) x).symm

theorem evaluation_norm (N : ℕ) (x : Circle) :
    ‖evaluation N x‖ = lebesgueConstant N := by
  rw [evaluation, integralFunctional_norm]
  exact integral_sub_left_eq_self (fun t => ‖kernel N t‖) haar x

theorem continuous_evaluation_norm : ContinuousEvaluationNorm := by
  intro N x
  exact ⟨evaluation N x, evaluation_apply N x, evaluation_norm N x⟩

def realEvaluation (N : ℕ) (x : Circle) : C(Circle, ℝ) →L[ℝ] ℝ :=
  integralFunctional ⟨fun t => realKernel N (x - t), by fun_prop⟩

theorem realEvaluation_apply (N : ℕ) (x : Circle) (f : C(Circle, ℝ)) :
    realEvaluation N x f = (partialSum N (fun t => (f t : ℂ)) x).re := by
  have h := real_fourier_convolution N f
    (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) x
  exact congrArg Complex.re h

theorem realEvaluation_norm (N : ℕ) (x : Circle) :
    ‖realEvaluation N x‖ = lebesgueConstant N := by
  rw [realEvaluation, integralFunctional_norm]
  change (∫ t, ‖realKernel N (x - t)‖ ∂haar) = lebesgueConstant N
  rw [integral_sub_left_eq_self (fun t => ‖realKernel N t‖) haar x]
  unfold lebesgueConstant
  apply integral_congr_ae
  exact ae_of_all haar fun t => by
    simpa only [Complex.norm_real] using congrArg norm (kernel_real N t)

theorem real_continuous_evaluation_norm : RealContinuousEvaluationNorm := by
  intro N x
  exact ⟨realEvaluation N x, realEvaluation_apply N x, realEvaluation_norm N x⟩

/-- The analytic estimate implies unbounded evaluation norms at every point. -/
theorem evaluationUnbounded_of_divergence (h : KernelNormDivergence) : EvaluationUnbounded := by
  intro x B
  obtain ⟨N, hN⟩ := (h.eventually_gt_atTop B).exists
  have hn : B < ‖evaluation N x‖ := by rwa [evaluation_norm]
  obtain ⟨f, hf, hbig⟩ := (evaluation N x).exists_lt_apply_of_lt_opNorm hn
  exact ⟨N, f, hf.le, by simpa only [evaluation_apply] using hbig⟩

/-- Specialization of the remaining continuous-kernel L¹ norm theorem.
The hypothesis is an explicit pending helper, not an assumed certificate. -/
theorem l1ConvolutionNorm_of_continuousKernelNorm
    (h : ∀ k : C(Circle, ℂ), ∃ S : DirichletKernelSpec.L1 →L[ℂ] DirichletKernelSpec.L1,
      (∀ f, (S f : Circle → ℂ) =ᵐ[haar]
        (fun x => ∫ t, k (x - t) * f t ∂haar)) ∧ ‖S‖ = ∫ t, ‖k t‖ ∂haar) :
    L1ConvolutionNorm := by
  intro N
  obtain ⟨S, hS, hn⟩ := h (kernel N)
  refine ⟨S, fun f => ?_, hn⟩
  exact Lp.ext ((hS f).trans (l1_representative N f).symm)

theorem realL1ConvolutionNorm_of_continuousKernelNorm
    (h : ∀ k : C(Circle, ℝ), ∃ S : RealL1 →L[ℝ] RealL1,
      (∀ f, (S f : Circle → ℝ) =ᵐ[haar]
        (fun x => ∫ t, k (x - t) * f t ∂haar)) ∧ ‖S‖ = ∫ t, ‖k t‖ ∂haar) :
    RealL1ConvolutionNorm := by
  intro N
  obtain ⟨S, hS, hn⟩ := h (realKernel N)
  refine ⟨S, hS, hn.trans ?_⟩
  apply integral_congr_ae
  exact ae_of_all haar fun t => by
    simpa only [Complex.norm_real] using congrArg norm (kernel_real N t)

theorem realEvaluationUnbounded_of_divergence (h : KernelNormDivergence) :
    RealEvaluationUnbounded := by
  intro x B
  obtain ⟨N, hN⟩ := (h.eventually_gt_atTop B).exists
  have hn : B < ‖realEvaluation N x‖ := by rwa [realEvaluation_norm]
  obtain ⟨f, hf, hbig⟩ := (realEvaluation N x).exists_lt_apply_of_lt_opNorm hn
  exact ⟨N, f, hf.le, by simpa only [realEvaluation_apply] using hbig⟩

theorem realConvolutionUnbounded_of_norm_and_divergence
    (hnorm : RealL1ConvolutionNorm) (hdiv : KernelNormDivergence) : RealConvolutionUnbounded := by
  intro B
  obtain ⟨N, hN⟩ := (hdiv.eventually_gt_atTop B).exists
  obtain ⟨S, hS, hn⟩ := hnorm N
  obtain ⟨f, hf, hbig⟩ := S.exists_lt_apply_of_lt_opNorm (by rwa [hn])
  exact ⟨N, S, f, hS, hf.le, hbig⟩

/-- Final L¹ unboundedness requires no additional analytic estimate. -/
theorem convolutionUnbounded_of_norm_and_divergence
    (hnorm : L1ConvolutionNorm) (hdiv : KernelNormDivergence) : ConvolutionUnbounded := by
  intro B
  obtain ⟨N, hN⟩ := (hdiv.eventually_gt_atTop B).exists
  obtain ⟨S, hS, hn⟩ := hnorm N
  obtain ⟨f, hf, hbig⟩ := S.exists_lt_apply_of_lt_opNorm (by rwa [hn])
  exact ⟨N, f, hf.le, by simpa only [hS] using hbig⟩

section L1Convolution
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The ordinary scalar convolution, before passing to the a.e. quotient. -/
def continuousKernelConvolution (k : C(Circle, 𝕜)) (f : Circle → 𝕜) : Circle → 𝕜 :=
  MeasureTheory.convolution f k (ContinuousLinearMap.mul 𝕜 𝕜) haar

theorem continuousKernel_integrable (k : C(Circle, 𝕜)) : Integrable k haar :=
  k.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem continuousKernelConvolution_integrable (k : C(Circle, 𝕜))
    {f : Circle → 𝕜} (hf : Integrable f haar) :
    Integrable (continuousKernelConvolution k f) haar :=
  hf.integrable_convolution (ContinuousLinearMap.mul 𝕜 𝕜) (continuousKernel_integrable k)

theorem continuousKernelConvolution_integral_bound (k : C(Circle, 𝕜))
    {f : Circle → 𝕜} (hf : Integrable f haar) :
    (∫ x, ‖continuousKernelConvolution k f x‖ ∂haar) ≤
      (∫ x, ‖k x‖ ∂haar) * (∫ t, ‖f t‖ ∂haar) := by
  have hk := continuousKernel_integrable k
  let g := MeasureTheory.convolution (fun t => ‖f t‖) (fun x => ‖k x‖)
    (ContinuousLinearMap.mul ℝ ℝ) haar
  have hg : Integrable g haar := hf.norm.integrable_convolution _ hk.norm
  calc
    _ ≤ ∫ x, g x ∂haar := by
      apply integral_mono (continuousKernelConvolution_integrable k hf).norm hg
      intro x
      simpa only [continuousKernelConvolution, g, MeasureTheory.convolution,
        ContinuousLinearMap.mul_apply', norm_mul] using
        norm_integral_le_integral_norm (μ := haar) (fun t => f t * k (x - t))
    _ = _ := by
      rw [integral_convolution _ hf.norm hk.norm]
      exact mul_comm _ _

/-- Convolution by a continuous kernel on the original scalar L¹ space. -/
def continuousKernelOperator (k : C(Circle, 𝕜)) : Lp 𝕜 1 haar →L[𝕜] Lp 𝕜 1 haar := by
  let A : Lp 𝕜 1 haar →ₗ[𝕜] Lp 𝕜 1 haar :=
    { toFun := fun f => (continuousKernelConvolution_integrable k (L1.integrable_coeFn f)).toL1 _
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [(continuousKernelConvolution_integrable k (L1.integrable_coeFn (f + g))).coeFn_toL1,
          Lp.coeFn_add
            ((continuousKernelConvolution_integrable k (L1.integrable_coeFn f)).toL1 _)
            ((continuousKernelConvolution_integrable k (L1.integrable_coeFn g)).toL1 _),
          (continuousKernelConvolution_integrable k (L1.integrable_coeFn f)).coeFn_toL1,
          (continuousKernelConvolution_integrable k (L1.integrable_coeFn g)).coeFn_toL1] with x hx ha hf hg
        rw [hx, ha]
        simp only [Pi.add_apply, hf, hg]
        unfold continuousKernelConvolution
        rw [MeasureTheory.convolution_congr _ (Lp.coeFn_add f g) (Filter.EventuallyEq.rfl)]
        exact congrFun (ConvolutionExists.add_distrib
          (ConvolutionExists.of_memLp_memLp (ContinuousLinearMap.mul 𝕜 𝕜) (Lp.memLp f) (k.continuous.memLp_top_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) haar))
          (ConvolutionExists.of_memLp_memLp (ContinuousLinearMap.mul 𝕜 𝕜) (Lp.memLp g) (k.continuous.memLp_top_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) haar))) x
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [(continuousKernelConvolution_integrable k (L1.integrable_coeFn (c • f))).coeFn_toL1,
          Lp.coeFn_smul c ((continuousKernelConvolution_integrable k (L1.integrable_coeFn f)).toL1 _),
          (continuousKernelConvolution_integrable k (L1.integrable_coeFn f)).coeFn_toL1] with x hx ha hf
        simp only [RingHom.id_apply]
        rw [hx, ha]
        simp only [Pi.smul_apply, hf]
        unfold continuousKernelConvolution
        rw [MeasureTheory.convolution_congr _ (Lp.coeFn_smul c f) (Filter.EventuallyEq.rfl)]
        exact congrFun (smul_convolution (L := ContinuousLinearMap.mul 𝕜 𝕜)) x }
  refine A.mkContinuous (∫ x, ‖k x‖ ∂haar) fun f => ?_
  change ‖(continuousKernelConvolution_integrable k (L1.integrable_coeFn f)).toL1 _‖ ≤ _
  rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm]
  have he : (fun x => ‖((continuousKernelConvolution_integrable k (L1.integrable_coeFn f)).toL1 _ : Circle → 𝕜) x‖) =ᵐ[haar]
      (fun x => ‖continuousKernelConvolution k f x‖) :=
    by
      filter_upwards [(continuousKernelConvolution_integrable k (L1.integrable_coeFn f)).coeFn_toL1] with x hx
      exact congrArg norm hx
  rw [integral_congr_ae he]
  exact continuousKernelConvolution_integral_bound k (L1.integrable_coeFn f)

theorem continuousKernelOperator_representative (k : C(Circle, 𝕜)) (f : Lp 𝕜 1 haar) :
    (continuousKernelOperator k f : Circle → 𝕜) =ᵐ[haar]
      (fun x => ∫ t, k (x - t) * f t ∂haar) := by
  refine (continuousKernelConvolution_integrable k (L1.integrable_coeFn f)).coeFn_toL1.trans ?_
  exact ae_of_all _ fun x => by
    unfold continuousKernelConvolution MeasureTheory.convolution
    simp only [ContinuousLinearMap.mul_apply', mul_comm]

theorem continuousKernelOperator_norm_le (k : C(Circle, 𝕜)) :
    ‖continuousKernelOperator k‖ ≤ ∫ x, ‖k x‖ ∂haar := by
  unfold continuousKernelOperator
  apply LinearMap.mkContinuous_norm_le
  exact integral_nonneg fun _ => norm_nonneg _

/-- A positive mass-one function supported in any prescribed small ball. -/
theorem exists_ball_density (δ : ℝ) (hδ : 0 < δ) :
    ∃ φ : Circle → ℝ, Integrable φ haar ∧ (∀ t, 0 ≤ φ t) ∧
      (∫ t, φ t ∂haar) = 1 ∧ Function.support φ ⊆ Metric.ball 0 δ := by
  let b : Set Circle := Metric.ball 0 δ
  have hb : MeasurableSet b := Metric.isOpen_ball.measurableSet
  have hm : 0 < haar.real b := ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos haar 0 hδ)) (measure_ne_top _ _)
  let φ : Circle → ℝ := b.indicator (fun _ => (haar.real b)⁻¹)
  refine ⟨φ, (integrable_const _).indicator hb, ?_, ?_, ?_⟩
  · intro t
    exact Set.indicator_nonneg (fun _ _ => inv_nonneg.mpr hm.le) t
  · change (∫ t, b.indicator (fun _ => (haar.real b)⁻¹) t ∂haar) = 1
    rw [integral_indicator_const _ hb, smul_eq_mul, mul_inv_cancel₀ hm.ne']
  · exact Set.support_indicator_subset

/-- Probability averages over a sufficiently small ball approximate a continuous
kernel uniformly. This also includes the zero kernel. -/
theorem exists_kernel_approximation (k : C(Circle, 𝕜)) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : Circle → 𝕜, Integrable f haar ∧ (∫ t, ‖f t‖ ∂haar) = 1 ∧
      ∀ x, ‖continuousKernelConvolution k f x - k x‖ ≤ ε := by
  obtain ⟨δ, hδ, hkδ⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous k.continuous) ε hε
  obtain ⟨φ, hφi, hφn, hφm, hφs⟩ := exists_ball_density δ hδ
  let f : Circle → 𝕜 := fun t => (φ t : 𝕜)
  have hfi : Integrable f haar := hφi.ofReal
  have hfn (t : Circle) : ‖f t‖ = φ t := by
    exact (RCLike.norm_ofReal _).trans (abs_of_nonneg (hφn t))
  have hfm : (∫ t, f t ∂haar) = 1 := by
    rw [show f = fun t => (φ t : 𝕜) from rfl, integral_ofReal, hφm, RCLike.ofReal_one]
  refine ⟨f, hfi, by simpa only [hfn] using hφm, ?_⟩
  intro x
  have hi : Integrable (fun t => f t * k (x - t)) haar :=
    ConvolutionExists.of_memLp_memLp (ContinuousLinearMap.mul 𝕜 𝕜) (memLp_one_iff_integrable.mpr hfi)
      (k.continuous.memLp_top_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) haar) x
  have he : continuousKernelConvolution k f x - k x =
      ∫ t, f t * (k (x - t) - k x) ∂haar := by
    simp only [mul_sub, integral_sub hi (hfi.mul_const (k x)), integral_mul_const, hfm, one_mul]
    rfl
  rw [he]
  calc
    _ ≤ ∫ t, φ t * ε ∂haar := by
      apply norm_integral_le_of_norm_le (hφi.mul_const ε)
      exact ae_of_all _ fun t => by
        rw [norm_mul, hfn]
        by_cases ht : φ t = 0
        · simp [ht]
        · apply mul_le_mul_of_nonneg_left _ (hφn t)
          rw [← dist_eq_norm]
          apply (hkδ ?_).le
          have hb := hφs (Function.mem_support.mpr ht)
          simpa only [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, sub_zero] using hb
    _ = ε := by rw [integral_mul_const, hφm, one_mul]

/-- The sharp L¹ norm for every continuous scalar kernel on the circle. -/
theorem continuousKernelOperator_norm (k : C(Circle, 𝕜)) :
    ‖continuousKernelOperator k‖ = ∫ x, ‖k x‖ ∂haar := by
  apply le_antisymm (continuousKernelOperator_norm_le k)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨f, hfi, hfn, hfe⟩ := exists_kernel_approximation k ε hε
  let v : Lp 𝕜 1 haar := hfi.toL1 f
  have hv : (v : Circle → 𝕜) =ᵐ[haar] f := hfi.coeFn_toL1
  have hvnorm : ‖v‖ = 1 := by
    rw [L1.norm_eq_integral_norm]
    calc
      _ = ∫ t, ‖f t‖ ∂haar := integral_congr_ae (by filter_upwards [hv] with x hx; rw [hx])
      _ = 1 := hfn
  have hSv : (continuousKernelOperator k v : Circle → 𝕜) =ᵐ[haar]
      continuousKernelConvolution k f := by
    refine (continuousKernelConvolution_integrable k (L1.integrable_coeFn v)).coeFn_toL1.trans ?_
    exact Filter.EventuallyEq.of_eq
      (MeasureTheory.convolution_congr _ hv Filter.EventuallyEq.rfl)
  have hn : (∫ x, ‖continuousKernelConvolution k f x‖ ∂haar) ≤ ‖continuousKernelOperator k‖ := by
    have ht := (continuousKernelOperator k).le_opNorm v
    rw [hvnorm, mul_one, L1.norm_eq_integral_norm] at ht
    have he : (∫ x, ‖(continuousKernelOperator k v : Circle → 𝕜) x‖ ∂haar) =
        ∫ x, ‖continuousKernelConvolution k f x‖ ∂haar :=
      integral_congr_ae (by filter_upwards [hSv] with x hx; rw [hx])
    rwa [he] at ht
  have he : (∫ x, ‖k x‖ ∂haar) ≤
      (∫ x, ‖continuousKernelConvolution k f x‖ ∂haar) + ε := by
    calc
      _ ≤ ∫ x, ‖continuousKernelConvolution k f x‖ + ε ∂haar := by
        apply integral_mono (continuousKernel_integrable k).norm
          ((continuousKernelConvolution_integrable k hfi).norm.add (integrable_const ε))
        intro x
        change ‖k x‖ ≤ ‖continuousKernelConvolution k f x‖ + ε
        have ht := norm_sub_norm_le (k x) (continuousKernelConvolution k f x)
        rw [norm_sub_rev] at ht
        linarith [hfe x]
      _ = _ := by rw [integral_add (continuousKernelConvolution_integrable k hfi).norm (integrable_const ε)]; simp
  linarith

end L1Convolution

/-- The original Fourier partial-sum operator has the sharp convolution norm. -/
theorem l1_convolution_norm : L1ConvolutionNorm := by
  apply l1ConvolutionNorm_of_continuousKernelNorm
  intro k
  exact ⟨continuousKernelOperator k, continuousKernelOperator_representative k,
    continuousKernelOperator_norm k⟩

theorem real_l1_convolution_norm : RealL1ConvolutionNorm := by
  apply realL1ConvolutionNorm_of_continuousKernelNorm
  intro k
  exact ⟨continuousKernelOperator k, continuousKernelOperator_representative k,
    continuousKernelOperator_norm k⟩


/-- Norm of the angular lift of the kernel. -/
def angularKernelNorm (N : ℕ) (t : ℝ) : ℝ := ‖kernel N (t : Circle)‖

theorem angularKernelNorm_continuous (N : ℕ) : Continuous (angularKernelNorm N) := by
  unfold angularKernelNorm
  fun_prop

theorem lebesgueConstant_interval (N : ℕ) :
    lebesgueConstant N = (2 * π)⁻¹ * ∫ t in 0..2 * π, angularKernelNorm N t := by
  unfold lebesgueConstant
  rw [AddCircle.integral_haarAddCircle]
  rw [← AddCircle.intervalIntegral_preimage (2 * π) 0]
  simp only [zero_add, smul_eq_mul, angularKernelNorm]

def periodMesh (N j : ℕ) : ℝ := (j : ℝ) * π / ((N : ℝ) + 1 / 2)

theorem frequency_pos (N : ℕ) : 0 < (N : ℝ) + 1 / 2 := by positivity

theorem periodMesh_nonneg (N j : ℕ) : 0 ≤ periodMesh N j := by
  unfold periodMesh; positivity

theorem periodMesh_mono (N : ℕ) : Monotone (periodMesh N) := by
  intro i j hij
  unfold periodMesh
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) Real.pi_pos.le)
    (frequency_pos N).le

theorem sine_square_integral_cell (N j : ℕ) :
    (∫ t in periodMesh N j..periodMesh N (j + 1),
      Real.sin (((N : ℝ) + 1 / 2) * t) ^ 2) = π / (2 * ((N : ℝ) + 1 / 2)) := by
  rw [intervalIntegral.integral_comp_mul_left (fun u => Real.sin u ^ 2) (frequency_pos N).ne']
  have ha : ((N : ℝ) + 1 / 2) * periodMesh N j = j * π := by
    unfold periodMesh; field_simp
  have hb : ((N : ℝ) + 1 / 2) * periodMesh N (j + 1) = ((j + 1 : ℕ) : ℝ) * π := by
    unfold periodMesh; field_simp
  rw [ha, hb, integral_sin_sq]
  simp only [Real.sin_nat_mul_pi, zero_mul, sub_zero, zero_add, smul_eq_mul]
  push_cast
  field_simp
  ring

/-- A division-free lower estimate, valid even at the zeros of the denominator. -/
theorem sine_square_le_weighted_kernel (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Real.sin (((N : ℝ) + 1 / 2) * t) ^ 2 ≤ t / 2 * angularKernelNorm N t := by
  have hs := congrArg norm (kernel_sine_product N t)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs] at hs
  have hd : |Real.sin (t / 2)| ≤ t / 2 :=
    (Real.abs_sin_le_abs).trans_eq (abs_of_nonneg (by positivity))
  have ha : Real.sin (((N : ℝ) + 1 / 2) * t) ^ 2 ≤
      |Real.sin (((N : ℝ) + 1 / 2) * t)| := by
    have h := Real.abs_sin_le_one (((N : ℝ) + 1 / 2) * t)
    nlinarith [sq_abs (Real.sin (((N : ℝ) + 1 / 2) * t)),
      abs_nonneg (Real.sin (((N : ℝ) + 1 / 2) * t))]
  apply ha.trans
  rw [← hs]
  exact mul_le_mul_of_nonneg_right hd (norm_nonneg _)

theorem kernel_integral_cell_lower (N j : ℕ) :
    ((j : ℝ) + 1)⁻¹ ≤
      ∫ t in periodMesh N j..periodMesh N (j + 1), angularKernelNorm N t := by
  have h := intervalIntegral.integral_mono_on (periodMesh_mono N (Nat.le_succ j))
    (show IntervalIntegrable (fun t => Real.sin (((N : ℝ) + 1 / 2) * t) ^ 2)
      volume (periodMesh N j) (periodMesh N (j + 1)) from (by fun_prop : Continuous _).intervalIntegrable _ _)
    (((angularKernelNorm_continuous N).const_mul (periodMesh N (j + 1) / 2)).intervalIntegrable _ _)
    (fun t ht => (sine_square_le_weighted_kernel N ((periodMesh_nonneg N j).trans ht.1)).trans
      (mul_le_mul_of_nonneg_right (by linarith [ht.2]) (norm_nonneg _)))
  rw [sine_square_integral_cell, intervalIntegral.integral_const_mul] at h
  have hp := frequency_pos N
  have hj : 0 < (j : ℝ) + 1 := by positivity
  unfold periodMesh at h
  have hmul : π / (2 * ((N : ℝ) + 1 / 2)) =
      (((j : ℝ) + 1) * π / ((N : ℝ) + 1 / 2) / 2) * ((j : ℝ) + 1)⁻¹ := by
    field_simp
  rw [Nat.cast_add, Nat.cast_one, hmul] at h
  simpa only [periodMesh, Nat.cast_add, Nat.cast_one] using
    (mul_le_mul_iff_right₀ (by positivity :
      0 < ((j : ℝ) + 1) * π / ((N : ℝ) + 1 / 2) / 2)).mp h

theorem harmonic_lower_bound (N : ℕ) :
    (harmonic (2 * N + 1) : ℝ) ≤ (2 * π) * lebesgueConstant N := by
  have he : periodMesh N (2 * N + 1) = 2 * π := by
    unfold periodMesh; push_cast; field_simp
  have hs := Finset.sum_le_sum (s := Finset.range (2 * N + 1))
    (fun j _ => kernel_integral_cell_lower N j)
  rw [intervalIntegral.sum_integral_adjacent_intervals
    (fun j _ => (angularKernelNorm_continuous N).intervalIntegrable _ _), he] at hs
  have h0 : periodMesh N 0 = 0 := by simp [periodMesh]
  rw [h0] at hs
  have hh : (harmonic (2 * N + 1) : ℝ) =
      ∑ j ∈ Finset.range (2 * N + 1), ((j : ℝ) + 1)⁻¹ := by
    simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Nat.cast_add, Nat.cast_one]
  rw [← hh] at hs
  rw [lebesgueConstant_interval]
  simpa only [← mul_assoc, mul_inv_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0), one_mul] using hs

theorem logarithmic_lower_bound (N : ℕ) :
    (2 * π)⁻¹ * Real.log (N + 2) ≤ lebesgueConstant N := by
  have hlog : Real.log (N + 2) ≤ Real.log (((2 * N + 1 + 1 : ℕ) : ℝ)) := by
    apply Real.log_le_log (by positivity)
    push_cast; linarith
  have h := hlog.trans ((log_add_one_le_harmonic (2 * N + 1)).trans (harmonic_lower_bound N))
  exact (inv_mul_le_iff₀ (by positivity : (0 : ℝ) < 2 * π)).2 h

theorem angularKernelNorm_even (N : ℕ) (t : ℝ) :
    angularKernelNorm N (-t) = angularKernelNorm N t := by
  have hk : kernel N (-(t : Circle)) = star (kernel N (t : Circle)) := by
    simp only [kernel, ContinuousMap.sum_apply, star_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [show -(t : Circle) = 0 - (t : Circle) by simp, fourier_sub]
    simp only [fourier_eval_zero, one_mul, fourier_neg]
    rfl
  unfold angularKernelNorm
  rw [AddCircle.coe_neg, hk, norm_star]

theorem lebesgueConstant_half_interval (N : ℕ) :
    lebesgueConstant N = π⁻¹ * ∫ t in 0..π, angularKernelNorm N t := by
  have h := AddCircle.intervalIntegral_preimage (2 * π) (-π)
    (fun x : Circle => ‖kernel N x‖)
  have he : -π + 2 * π = π := by ring
  rw [he] at h
  have hn := intervalIntegral.integral_comp_neg (angularKernelNorm N) (a := 0) (b := π)
  simp only [neg_zero, angularKernelNorm_even] at hn
  have ha := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((angularKernelNorm_continuous N).intervalIntegrable (-π) 0)
    ((angularKernelNorm_continuous N).intervalIntegrable 0 π)
  unfold lebesgueConstant
  rw [AddCircle.integral_haarAddCircle, ← h]
  change (2 * π)⁻¹ * (∫ t in -π..π, angularKernelNorm N t) = _
  rw [← ha, ← hn]
  field_simp
  ring

theorem angularKernelNorm_le_pi_div (N : ℕ) {t : ℝ} (ht : 0 < t) (htπ : t ≤ π) :
    angularKernelNorm N t ≤ π / t := by
  have hd : t / π ≤ Real.sin (t / 2) := by
    have h := Real.mul_le_sin (x := t / 2) (by positivity) (by linarith)
    convert h using 1; ring
  have hs : 0 < Real.sin (t / 2) := lt_of_lt_of_le (div_pos ht Real.pi_pos) hd
  have h := congrArg norm (kernel_sine_product N t)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hs] at h
  change Real.sin (t / 2) * angularKernelNorm N t = _ at h
  have hu := Real.abs_sin_le_one (((N : ℝ) + 1 / 2) * t)
  have hn : 0 ≤ angularKernelNorm N t := norm_nonneg _
  have hm : t / π * angularKernelNorm N t ≤ 1 :=
    (mul_le_mul_of_nonneg_right hd hn).trans (h.le.trans hu)
  apply (le_div_iff₀ ht).2
  rw [div_mul_eq_mul_div] at hm
  have hm' := (div_le_iff₀ Real.pi_pos).mp hm
  nlinarith

theorem logarithmic_upper_bound_aux (N : ℕ) :
    lebesgueConstant N ≤ 1 + Real.log (2 * N + 1) := by
  let M : ℝ := 2 * N + 1
  let δ : ℝ := π / M
  have hM : 0 < M := by dsimp [M]; positivity
  have hM1 : 1 ≤ M := by dsimp [M]; nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hδ : 0 < δ := div_pos Real.pi_pos hM
  have hδπ : δ ≤ π := by
    dsimp [δ]
    exact div_le_self Real.pi_pos.le hM1
  have hfirst : (∫ t in 0..δ, angularKernelNorm N t) ≤ π := by
    calc
      _ ≤ ∫ _ in (0 : ℝ)..δ, M :=
        intervalIntegral.integral_mono hδ.le
          ((angularKernelNorm_continuous N).intervalIntegrable _ _)
          (intervalIntegrable_const) (fun t => kernel_bound N (t : Circle))
      _ = π := by simp [intervalIntegral.integral_const, δ, smul_eq_mul]; field_simp
  have hi : IntervalIntegrable (fun t : ℝ => π / t) volume δ π := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht
    have htδ : δ ≤ t := by rw [Set.uIcc_of_le hδπ] at ht; exact ht.1
    exact ne_of_gt (hδ.trans_le htδ)
  have hsecond : (∫ t in δ..π, angularKernelNorm N t) ≤ π * Real.log M := by
    calc
      _ ≤ ∫ t in δ..π, π / t :=
        intervalIntegral.integral_mono_on hδπ
          ((angularKernelNorm_continuous N).intervalIntegrable _ _) hi
          (fun t ht => angularKernelNorm_le_pi_div N (hδ.trans_le ht.1) ht.2)
      _ = π * Real.log M := by
        simp_rw [div_eq_mul_inv]
        rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hδ Real.pi_pos]
        congr 2
        dsimp [δ]
        field_simp
  rw [lebesgueConstant_half_interval]
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((angularKernelNorm_continuous N).intervalIntegrable 0 δ)
    ((angularKernelNorm_continuous N).intervalIntegrable δ π)
  rw [← hadd]
  apply (inv_mul_le_iff₀ Real.pi_pos).2
  dsimp [M] at hsecond
  nlinarith

theorem logarithmic_bounds : LogarithmicBounds := by
  refine ⟨(2 * π)⁻¹, 2 + (Real.log 2)⁻¹, by positivity, ?_, fun N =>
    ⟨logarithmic_lower_bound N, ?_⟩⟩
  · have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  · have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hl : Real.log 2 ≤ Real.log (N + 2) :=
      Real.log_le_log (by norm_num) (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
    have hm : Real.log (2 * N + 1) ≤ Real.log 2 + Real.log (N + 2) := by
      rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (N : ℝ) + 2 ≠ 0)]
      exact Real.log_le_log (by positivity) (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
    have hone : 1 ≤ (Real.log 2)⁻¹ * Real.log (N + 2) := by
      exact (le_inv_mul_iff₀ hp).2 (by simpa using hl)
    have hu := logarithmic_upper_bound_aux N
    nlinarith

theorem kernel_norm_divergence : KernelNormDivergence :=
  kernelNormDivergence_of_logarithmicBounds logarithmic_bounds

theorem evaluation_unbounded : EvaluationUnbounded :=
  evaluationUnbounded_of_divergence kernel_norm_divergence

theorem real_evaluation_unbounded : RealEvaluationUnbounded :=
  realEvaluationUnbounded_of_divergence kernel_norm_divergence

theorem convolution_unbounded : ConvolutionUnbounded :=
  convolutionUnbounded_of_norm_and_divergence l1_convolution_norm kernel_norm_divergence

theorem real_convolution_unbounded : RealConvolutionUnbounded :=
  realConvolutionUnbounded_of_norm_and_divergence real_l1_convolution_norm kernel_norm_divergence

end ExpandedFA.PartIV.DirichletKernel
