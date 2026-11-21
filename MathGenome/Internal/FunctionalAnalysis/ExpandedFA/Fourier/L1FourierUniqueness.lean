import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.L1FourierUniqueness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.SchwartzFourierInversion
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.ConvolutionEndpointBounds
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Fourier uniqueness for L¹ functions and finite positive measures, with
explicit 2π/angular normalization and Gaussian approximation in L¹.
The uniqueness proof uses Schwartz inversion and smooth compact tests;
Gaussian approximation is proved separately by translation continuity. -/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory Filter
open scoped Topology FourierTransform SchwartzMap ENNReal
namespace ExpandedFA.Fourier
namespace Uniqueness
open Specs.ExpandedFA.Fourier.L1FourierUniqueness

lemma weighted_eq_native {d : ℕ} (μ : Measure (Euclidean d)) (f : Euclidean d → ℂ)
    (ξ : Euclidean d) :
    weightedIntegralFourier μ f ξ =
      VectorFourier.fourierIntegral Real.fourierChar μ (innerₗ (Euclidean d)) f ξ := by
  unfold weightedIntegralFourier VectorFourier.fourierIntegral
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Real.fourierChar_apply, Circle.smul_def, smul_eq_mul]
  congr 2
  change -2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x ξ : ℝ) = _
  simp only [innerₗ_apply_apply]
  push_cast
  ring

lemma weighted_pairing {d : ℕ} (μ : Measure (Euclidean d)) [SigmaFinite μ]
    (f : Euclidean d → ℂ) (hf : Integrable f μ) (φ : Schwartz ℂ d) :
    (∫ ξ, weightedIntegralFourier μ f ξ * φ ξ) =
      ∫ x, f x * schwartzFourier φ x ∂μ := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ (Euclidean d)) Real.continuous_fourierChar continuous_inner hf (φ.integrable (μ := volume))
  simp_rw [weighted_eq_native]
  simpa only [smul_eq_mul, flip_innerₗ, schwartzFourier,
    FourierTransform.fourierCLM_apply, SchwartzMap.fourier_coe, Real.fourier_eq,
    VectorFourier.fourierIntegral, innerₗ_apply_apply] using h

theorem weighted_uniqueness : WeightedUniqueness := by
  intro d μ _ f hf hzero
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable
  intro g hg hc
  let φ : Schwartz ℂ d := (hc.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hg)
  let ψ : Schwartz ℂ d := 𝓕⁻ φ
  have hφ : schwartzFourier ψ = φ := by
    simpa only [ψ, schwartzFourier, FourierTransform.fourierCLM_apply] using
      FourierTransform.fourier_fourierInv_eq φ
  have hp := weighted_pairing μ f hf ψ
  simp only [hzero, zero_mul, integral_zero, hφ] at hp
  calc
    _ = ∫ x, f x * φ x ∂μ := ?_
    _ = 0 := hp.symm
  apply integral_congr_ae
  filter_upwards [] with x
  simp [φ, mul_comm, RCLike.real_smul_eq_coe_mul]

theorem l1_uniqueness : L1Uniqueness := by
  intro d f hf hzero
  exact weighted_uniqueness d volume f hf hzero

theorem l1_injectivity : L1Injectivity := by
  intro d f g hf hg heq
  have h : ∀ ξ, integralFourier (f-g) ξ = 0 := by
    intro ξ
    simp only [integralFourier_eq_native, Real.fourier_eq, Pi.sub_apply, smul_sub]
    rw [integral_sub ((Real.fourierIntegral_convergent_iff ξ).mpr hf)
      ((Real.fourierIntegral_convergent_iff ξ).mpr hg)]
    have hh := heq ξ
    simpa only [integralFourier_eq_native, Real.fourier_eq] using sub_eq_zero.mpr hh
  filter_upwards [l1_uniqueness d (f-g) (hf.sub hg) h] with x hx
  exact sub_eq_zero.mp hx

theorem real_l1_uniqueness : RealL1Uniqueness := by
  intro d f hf hz
  filter_upwards [l1_uniqueness d (fun x => (f x : ℂ)) hf.ofReal hz] with x hx
  exact Complex.ofReal_eq_zero.mp hx

theorem angular_uniqueness : AngularUniqueness := by
  intro d f hf hz
  apply l1_uniqueness d f hf
  intro ξ
  have h := hz ((2 * Real.pi) • ξ)
  rw [angular_normalization] at h
  simpa [smul_smul, inv_mul_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)] using h

theorem continuous_uniqueness : ContinuousUniqueness := by
  intro d f hf hc hz
  have h := l1_uniqueness d f hf hz
  exact fun x => congrFun (Measure.eq_of_ae_eq h hc continuous_zero) x

theorem finite_measure_uniqueness : FiniteMeasureUniqueness := by
  intro d μ ν _ _ heq
  apply Measure.ext_of_charFun
  funext t
  have h := heq (-((2 * Real.pi)⁻¹ • t))
  rw [charFun_eq_fourierIntegral', charFun_eq_fourierIntegral']
  simpa only [finiteMeasureFourier, weighted_eq_native, neg_smul, Pi.one_def] using h

lemma angular_measure_normalization {d : ℕ} (μ : Measure (Euclidean d)) (p : Euclidean d) :
    (∫ x, Complex.exp (-Complex.I * (inner ℝ x p : ℝ)) ∂μ) =
      finiteMeasureFourier μ ((2 * Real.pi)⁻¹ • p) := by
  unfold finiteMeasureFourier weightedIntegralFourier
  apply integral_congr_ae
  filter_upwards [] with x
  rw [mul_one, inner_smul_right]
  congr 1
  push_cast
  field_simp

theorem angular_finite_measure_uniqueness : AngularFiniteMeasureUniqueness := by
  intro d μ ν _ _ hz
  apply finite_measure_uniqueness d μ ν
  intro ξ
  have h := hz ((2 * Real.pi) • ξ)
  simp only [angular_measure_normalization, smul_smul,
    inv_mul_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero), one_smul] at h
  exact h

theorem gaussian_vanishing : GaussianVanishing := by
  intro d f hf hz c x
  apply integral_eq_zero_of_ae
  filter_upwards [l1_uniqueness d f hf hz] with y hy
  simp only [Pi.zero_apply] at hy
  simp only [hy, mul_zero, Pi.zero_apply]

theorem gaussian_continuous_approximation : GaussianContinuousApproximation := by
  intro d f hf x hx
  simpa [gaussianSmooth, gaussianKernel, smul_eq_mul, finrank_euclideanSpace] using
    Real.tendsto_integral_gaussian_smul' hf hx

theorem gaussian_fourier_approximation : GaussianFourierApproximation := by
  intro d f hf hF x
  have heq : integralFourier f = 𝓕 f := funext (integralFourier_eq_native f)
  rw [heq] at hF ⊢
  simpa [gaussianSmooth, gaussianKernel, smul_eq_mul, finrank_euclideanSpace] using
    Real.tendsto_integral_gaussian_smul hf hF x

/-- Translation error in the ordinary L¹ norm, as an extended nonnegative real. -/
def translationError {d : ℕ} (f : Euclidean d → ℂ) (h : Euclidean d) : ℝ≥0∞ :=
  eLpNorm (fun x => f (x-h) - f x) 1 volume

lemma translationError_continuous {d : ℕ} (f : Euclidean d → ℂ) (hf : Integrable f) :
    Continuous (translationError f) := by
  let v := (memLp_one_iff_integrable.mpr hf).toLp f
  let T (h : Euclidean d) := Lp.compMeasurePreserving (fun x => x-h)
    (measurePreserving_sub_right volume h) v
  have hT : Continuous T := by
    let g : Euclidean d → C(Euclidean d, Euclidean d) :=
      fun h => ⟨fun x => x-h, continuous_id.sub continuous_const⟩
    exact continuous_const.compMeasurePreservingLp
      (ContinuousMap.continuous_of_continuous_uncurry g
        (continuous_snd.sub continuous_fst))
      (fun h => measurePreserving_sub_right volume h) (by norm_num)
  have heq (h : Euclidean d) : translationError f h = ‖T h - v‖ₑ := by
    rw [Lp.enorm_def]
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_sub (T h) v,
      Lp.coeFn_compMeasurePreserving v (measurePreserving_sub_right volume h),
      (measurePreserving_sub_right volume h).quasiMeasurePreserving.ae
        (memLp_one_iff_integrable.mpr hf).coeFn_toLp,
      (memLp_one_iff_integrable.mpr hf).coeFn_toLp] with x hs ht hf' hv
    change (T h - v) x = (T h) x - v x at hs
    change (T h) x = v (x-h) at ht
    change v (x-h) = f (x-h) at hf'
    change v x = f x at hv
    rw [ht, hf', hv] at hs
    exact hs.symm
  have hc : Continuous (fun h => ‖T h - v‖ₑ) := (hT.sub continuous_const).enorm
  exact hc.congr (fun h => (heq h).symm)

lemma translationError_bound {d : ℕ} (f : Euclidean d → ℂ) (hf : Integrable f)
    (h : Euclidean d) : translationError f h ≤ 2 * eLpNorm f 1 volume := by
  apply (eLpNorm_sub_le (by norm_num : (1 : ℝ≥0∞) ≤ 1)).trans
  rw [← Function.comp_def, eLpNorm_comp_measurePreserving hf.aestronglyMeasurable
    (measurePreserving_sub_right volume h), two_mul]

lemma translationError_zero {d : ℕ} (f : Euclidean d → ℂ) : translationError f 0 = 0 := by
  simp [translationError]

/-- Any integrable mass-one kernel gives L¹ convergence of averaged translates. -/
lemma average_l1_of_measurable {d : ℕ} (g : Euclidean d → ℝ) (hg : Measurable g)
    (hgi : Integrable g) (hgm : ∫ y, g y = 1)
    (f : Euclidean d → ℂ) (hfm : Measurable f) (hf : Integrable f) :
    Tendsto (fun ε : ℝ => eLpNorm ((fun x => ∫ y, g y • f (x-ε • y)) - f) 1 volume)
      (𝓝 (0 : ℝ)) (𝓝 0) := by
  let B (ε : ℝ) := ∫⁻ y, ‖g y‖ₑ * translationError f (ε • y)
  have hfinite : (∫⁻ y, ‖g y‖ₑ * (2 * eLpNorm f 1 volume)) ≠ ∞ := by
    rw [lintegral_mul_const _ hg.enorm]
    exact ENNReal.mul_ne_top hgi.hasFiniteIntegral.ne
      (ENNReal.mul_ne_top (by norm_num) (memLp_one_iff_integrable.mpr hf).eLpNorm_ne_top)
  have hB : Tendsto B (𝓝 (0 : ℝ)) (𝓝 0) := by
    have ht : Tendsto (fun ε : ℝ => ∫⁻ y, ‖g y‖ₑ * translationError f (ε • y))
        (𝓝 0) (𝓝 (∫⁻ _y : Euclidean d, (0 : ℝ≥0∞))) := by
      apply tendsto_lintegral_filter_of_dominated_convergence
        (fun y => ‖g y‖ₑ * (2 * eLpNorm f 1 volume))
      · apply Filter.Eventually.of_forall
        intro ε
        exact hg.enorm.mul ((translationError_continuous f hf).measurable.comp
          ((measurable_const (a := ε)).smul measurable_id))
      · apply Filter.Eventually.of_forall
        intro ε
        apply Filter.Eventually.of_forall
        intro y
        gcongr
        exact translationError_bound f hf (ε • y)
      · exact hfinite
      · apply Filter.Eventually.of_forall
        intro y
        have ht : Tendsto (fun ε : ℝ => translationError f (ε • y)) (𝓝 0) (𝓝 0) := by
          have hs : Tendsto (fun ε : ℝ => ε • y) (𝓝 0) (𝓝 (0 : Euclidean d)) := by
            have hsc : Continuous (fun ε : ℝ => ε • y) := by fun_prop
            simpa only [zero_smul] using hsc.tendsto (0 : ℝ)
          simpa only [Function.comp_def, translationError_zero] using
            ((translationError_continuous f hf).tendsto 0).comp hs
        simpa only [mul_zero] using
          (ENNReal.Tendsto.const_mul (a := ‖g y‖ₑ) ht (Or.inr (by simp)))
    simpa only [lintegral_zero] using ht
  have hle (ε : ℝ) :
      eLpNorm ((fun x => ∫ y, g y • f (x-ε • y)) - f) 1 volume ≤ B ε := by
    let F : Euclidean d × Euclidean d → ℂ := fun z => g z.2 • (f (z.1-ε • z.2) - f z.1)
    have hF : Measurable F := (hg.comp measurable_snd).smul
      ((hfm.comp (measurable_fst.sub ((measurable_const (a := ε)).smul measurable_snd))).sub
        (hfm.comp measurable_fst))
    have hn : (∫⁻ y, eLpNorm (fun x => F (x,y)) 1 volume) = B ε := by
      apply lintegral_congr
      intro y
      exact eLpNorm_const_smul (g y) (fun x => f (x-ε • y) - f x) 1 volume
    have hBfin : B ε < ∞ := by
      apply lt_of_le_of_lt (lintegral_mono fun y =>
        (by gcongr; exact translationError_bound f hf (ε • y))) (lt_top_iff_ne_top.mpr hfinite)
    obtain ⟨hi, hb⟩ := Distributions.minkowski_integral_eLpNorm volume volume 1
      le_rfl (by norm_num) F hF (by rw [hn]; exact hBfin)
    rw [hn] at hb
    apply le_trans (le_of_eq ?_) hb
    apply eLpNorm_congr_ae
    filter_upwards [hi] with x hx
    have hc : Integrable (fun y => g y • f x) := hgi.smul_const _
    have hc' : Integrable (fun y => g y • f (x-ε • y)) := by
      convert hx.add hc using 1
      ext y
      simp [F, smul_sub]
    change (∫ y, g y • f (x-ε • y)) - f x = ∫ y, g y • (f (x-ε • y) - f x)
    simp_rw [smul_sub]
    rw [integral_sub hc' hc, integral_smul_const, hgm, one_smul]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB
    (fun _ => bot_le) hle

theorem gaussian_mass : GaussianMass := by
  intro d
  have hm : (∫ y, standardGaussian d y) = 1 := by
    simpa [standardGaussian, finrank_euclideanSpace] using
      GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Euclidean d) Real.pi_pos
  exact ⟨fun y => Real.exp_pos _, integrable_of_integral_eq_one hm, hm⟩

lemma average_convolution {d : ℕ} (g : Euclidean d → ℝ) (ε : ℝ) (hε : 0 < ε)
    (f : Euclidean d → ℂ) (x : Euclidean d) :
    (∫ y, g y • f (x-ε • y)) =
      ∫ y, ((ε ^ d)⁻¹ * g (ε⁻¹ • (x-y))) • f y := by
  let H : Euclidean d → ℂ := fun y => g (ε⁻¹ • y) • f (x-y)
  calc
    _ = ∫ y, H (ε • y) := by simp [H, inv_smul_smul₀ hε.ne']
    _ = (ε ^ d)⁻¹ • ∫ y, H y := by
      simpa [finrank_euclideanSpace] using
        Measure.integral_comp_smul_of_nonneg volume H ε (hR := hε.le)
    _ = ∫ y, (ε ^ d)⁻¹ • H y := (integral_smul _ _).symm
    _ = _ := by
      rw [← integral_sub_left_eq_self (fun y => (ε ^ d)⁻¹ • H y) volume x]
      simp only [H, sub_sub_cancel, smul_smul]

theorem gaussian_average_convolution : GaussianAverageConvolution := by
  intro d ε hε f x
  exact average_convolution (standardGaussian d) ε hε f x

lemma average_integrable {d : ℕ} (g : Euclidean d → ℝ) (hg : Measurable g)
    (hgi : Integrable g) (f : Euclidean d → ℂ) (hfm : Measurable f) (hf : Integrable f)
    (ε : ℝ) : Integrable (fun x => ∫ y, g y • f (x-ε • y)) := by
  let F : Euclidean d × Euclidean d → ℂ := fun z => g z.2 • f (z.1-ε • z.2)
  have hF : Measurable F := (hg.comp measurable_snd).smul
    (hfm.comp (measurable_fst.sub ((measurable_const (a := ε)).smul measurable_snd)))
  have hn : (∫⁻ y, eLpNorm (fun x => F (x,y)) 1 volume) =
      (∫⁻ y, ‖g y‖ₑ) * eLpNorm f 1 volume := by
    change (∫⁻ y, eLpNorm (g y • fun x => f (x-ε • y)) 1 volume) = _
    simp_rw [eLpNorm_const_smul]
    have he (y : Euclidean d) : eLpNorm (fun x => f (x-ε • y)) 1 volume =
        eLpNorm f 1 volume :=
      eLpNorm_comp_measurePreserving hf.aestronglyMeasurable
        (measurePreserving_sub_right volume (ε • y))
    simp_rw [he]
    exact lintegral_mul_const _ hg.enorm
  have hfin : (∫⁻ y, eLpNorm (fun x => F (x,y)) 1 volume) < ∞ := by
    rw [hn]
    exact ENNReal.mul_lt_top hgi.hasFiniteIntegral
      (memLp_one_iff_integrable.mpr hf).eLpNorm_lt_top
  have hb := (Distributions.minkowski_integral_eLpNorm volume volume 1 le_rfl
    (by norm_num) F hF hfin).2
  apply memLp_one_iff_integrable.mp
  exact hb.trans_lt hfin

lemma gaussianAverage_congr {d : ℕ} {f f' : Euclidean d → ℂ}
    (hff : f =ᵐ[volume] f') {ε : ℝ} (hε : 0 < ε) :
    gaussianAverage ε f = gaussianAverage ε f' := by
  funext x
  apply integral_congr_ae
  have ha := ((volume.measurePreserving_sub_left x).quasiMeasurePreserving.comp
    (Measure.quasiMeasurePreserving_smul volume hε.ne')).ae hff
  filter_upwards [ha] with y hy
  exact congrArg (fun z => standardGaussian d y • z) hy

theorem gaussian_integrability : GaussianIntegrability := by
  intro d f hf ε hε
  let f' := hf.aestronglyMeasurable.mk f
  have hff : f =ᵐ[volume] f' := hf.aestronglyMeasurable.ae_eq_mk
  have hfm : Measurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  rw [gaussianAverage_congr hff hε]
  apply average_integrable (standardGaussian d) (by unfold standardGaussian; fun_prop)
    (gaussian_mass d).2.1 f' hfm (hf.congr hff)

theorem gaussian_l1_approximation : GaussianL1Approximation := by
  intro d f hf
  let f' := hf.aestronglyMeasurable.mk f
  have hff : f =ᵐ[volume] f' := hf.aestronglyMeasurable.ae_eq_mk
  have hfm : Measurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hg : Measurable (standardGaussian d) := by
    unfold standardGaussian
    fun_prop
  have ht := (average_l1_of_measurable (standardGaussian d) hg
    (gaussian_mass d).2.1 (gaussian_mass d).2.2 f' hfm (hf.congr hff)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  apply eLpNorm_congr_ae
  have hc := gaussianAverage_congr hff hε
  exact ((EventuallyEq.of_eq hc).sub hff).symm

end Uniqueness
end ExpandedFA.Fourier
