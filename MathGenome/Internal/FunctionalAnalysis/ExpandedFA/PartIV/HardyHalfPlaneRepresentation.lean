import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyHalfPlaneRepresentation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform
namespace ExpandedFA.PartIV.HardyHalfPlaneRepresentation
open HardyHalfPlaneRepresentationSpec

lemma norm_kernel (z : ℂ) (t : ℝ) :
    ‖kernel z t‖ = Real.exp (-2 * Real.pi * z.im * t) := by
  rw [kernel, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

lemma kernel_memLp (z : ℂ) (hz : z ∈ upperHalfPlane) :
    MemLp (kernel z) 2 positiveMeasure := by
  apply (memLp_two_iff_integrable_sq_norm (by unfold kernel; fun_prop)).mpr
  have h := integrableOn_exp_mul_complex_Ioi
    (a := ((-4 * Real.pi * z.im : ℝ) : ℂ)) (by
      simp only [Complex.ofReal_re]
      have := hz
      change 0 < z.im at this
      nlinarith [Real.pi_pos]) (0 : ℝ)
  have hn := h.norm
  convert hn using 1
  ext t
  rw [norm_kernel, ← Real.exp_nat_mul]
  simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  congr 1
  ring

theorem absolute_convergence : AbsoluteConvergence := by
  intro f hf z hz
  exact (kernel_memLp z hz).integrable_mul hf

lemma damp_norm_le {y t : ℝ} (hy : 0 ≤ y) (ht : 0 ≤ t) (f : ℝ → ℂ) :
    ‖damp f y t‖ ≤ ‖f t‖ := by
  have h : Real.exp (-2 * Real.pi * y * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      have : 0 ≤ 2 * Real.pi * y * t := by positivity
      nlinarith)
  simpa only [damp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] using mul_le_of_le_one_left (norm_nonneg (f t)) h

theorem damping_bound : DampingBound := by
  intro f hf y hy
  have hle : ∀ᵐ t ∂positiveMeasure, ‖damp f y t‖ ≤ ‖f t‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact damp_norm_le hy (le_of_lt ht) f
  have hm : AEStronglyMeasurable (damp f y) positiveMeasure := by
    exact (by fun_prop : Continuous (fun t : ℝ =>
      (Real.exp (-2 * Real.pi * y * t) : ℂ))).aestronglyMeasurable.mul hf.aestronglyMeasurable
  exact ⟨hf.mono hm hle, eLpNorm_mono_ae hm hle⟩

lemma damp_measurable (f : ℝ → ℂ) (hf : MemLp f 2 positiveMeasure) (y : ℝ) :
    AEStronglyMeasurable (damp f y) positiveMeasure :=
  (by fun_prop : Continuous (fun t : ℝ =>
    (Real.exp (-2 * Real.pi * y * t) : ℂ))).aestronglyMeasurable.mul hf.aestronglyMeasurable

theorem damping_convergence : DampingConvergence := by
  intro f hf
  have hmeas (y : ℝ) : AEStronglyMeasurable (damp f y - f) positiveMeasure :=
    (damp_measurable f hf y).sub hf.aestronglyMeasurable
  have hbound : ∀ᶠ y : ℝ in 𝓝[>] 0, ∀ᵐ t ∂positiveMeasure,
      ‖damp f y t - f t‖ₑ ^ (2 : ℝ) ≤ ‖(2 : ℂ) * f t‖ₑ ^ (2 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    rw [← ofReal_norm, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    calc
      ‖damp f y t - f t‖ ≤ ‖damp f y t‖ + ‖f t‖ := norm_sub_le _ _
      _ ≤ ‖f t‖ + ‖f t‖ := by gcongr; exact damp_norm_le (le_of_lt hy) (le_of_lt ht) f
      _ = ‖(2 : ℂ) * f t‖ := by rw [norm_mul]; norm_num; ring
  have hfin : (∫⁻ t, ‖(2 : ℂ) * f t‖ₑ ^ (2 : ℝ) ∂positiveMeasure) ≠ ∞ := by
    exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)
      (hf.const_mul (2 : ℂ))).ne
  have hlim : ∀ᵐ t ∂positiveMeasure,
      Tendsto (fun y : ℝ => ‖damp f y t - f t‖ₑ ^ (2 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    filter_upwards [] with t
    have hc : Continuous (fun y : ℝ => damp f y t - f t) := by
      unfold damp
      fun_prop
    have hh : Tendsto (fun y : ℝ => damp f y t - f t) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
      simpa [damp] using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa only [Function.comp_def, enorm_eq_nnnorm, nnnorm_zero, ENNReal.coe_zero,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] using
      (ENNReal.continuous_rpow_const (y := (2 : ℝ))).continuousAt.tendsto.comp
        (ENNReal.tendsto_coe.mpr hh.nnnorm)
  have hI : Tendsto (fun y : ℝ =>
      ∫⁻ t, ‖damp f y t - f t‖ₑ ^ (2 : ℝ) ∂positiveMeasure) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_lintegral_filter_of_dominated_convergence'
      (fun t => ‖(2 : ℂ) * f t‖ₑ ^ (2 : ℝ))
      (Eventually.of_forall (fun y => (hmeas y).enorm.pow_const _))
      hbound hfin hlim
  have hpow := (ENNReal.continuous_rpow_const (y := (1 / (2 : ℝ)))).continuousAt.tendsto.comp hI
  simpa only [Function.comp_def, Pi.sub_apply, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num) (hmeas _), ENNReal.toReal_ofNat, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    using hpow

/-- The first polynomial weight still has an exponentially integrable square. -/
lemma weighted_exp_memLp {a : ℝ} (ha : 0 < a) :
    MemLp (fun t : ℝ => t * Real.exp (-a * t)) 2 positiveMeasure := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (2 : ℝ)) (p := (1 : ℝ)) (b := 2 * a) (by norm_num) (by norm_num) (by positivity)
  simp only [Real.rpow_two, Real.rpow_one] at h
  change Integrable (fun x : ℝ => x ^ 2 * Real.exp (-(2 * a) * x)) positiveMeasure at h
  apply h.congr
  filter_upwards [] with t
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  ring

lemma kernel_derivative (f : ℝ → ℂ) (t : ℝ) (z : ℂ) :
    HasDerivAt (fun w => kernel w t * f t)
      ((2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) * kernel z t * f t) z := by
  have h := (((hasDerivAt_id z).const_mul
    (2 * (Real.pi : ℂ) * Complex.I)).mul_const (t : ℂ)).cexp.mul_const (f t)
  convert h using 1 <;> dsimp only [kernel, id_eq]; ring

/-- Holomorphy is derived from the integral, with no boundary regularity premise. -/
theorem laplace_differentiableOn (f : ℝ → ℂ) (hf : MemLp f 2 positiveMeasure) :
    DifferentiableOn ℂ (laplace f) upperHalfPlane := by
  intro z hz
  have hzi : 0 < z.im := hz
  let s : Set ℂ := {w | z.im / 2 < w.im}
  have hs : s ∈ 𝓝 z := (isOpen_lt continuous_const Complex.continuous_im).mem_nhds
    (show z.im / 2 < z.im by linarith)
  let B : ℝ → ℝ := fun t => 2 * Real.pi *
    (t * Real.exp (-(Real.pi * z.im) * t)) * ‖f t‖
  have hB : Integrable B positiveMeasure := by
    simpa only [B, Pi.mul_apply, mul_assoc] using
      ((weighted_exp_memLp (mul_pos Real.pi_pos hzi)).integrable_mul hf.norm).const_mul
        (2 * Real.pi)
  let K' : ℂ → ℝ → ℂ := fun w t =>
    (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) * kernel w t * f t
  have hmeas (w : ℂ) : AEStronglyMeasurable (fun t => kernel w t * f t) positiveMeasure := by
    exact (by unfold kernel; fun_prop : Continuous (kernel w)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable (K' z) positiveMeasure := by
    exact (by unfold kernel; fun_prop : Continuous (fun t : ℝ =>
      (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) * kernel z t)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  have hbound : ∀ᵐ t ∂positiveMeasure, ∀ w ∈ s, ‖K' w t‖ ≤ B t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro w hw
    have ht0 : 0 ≤ t := le_of_lt ht
    have hexp : Real.exp (-2 * Real.pi * w.im * t) ≤
        Real.exp (-(Real.pi * z.im) * t) := by
      apply Real.exp_le_exp.mpr
      have hh : z.im / 2 ≤ w.im := le_of_lt hw
      nlinarith [Real.pi_pos, mul_nonneg Real.pi_pos.le ht0]
    have hcoef : ‖2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)‖ = 2 * Real.pi * t := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        abs_of_nonneg ht0]
    dsimp only [K', B]
    rw [norm_mul, norm_mul, hcoef, norm_kernel]
    nlinarith [mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 2 * Real.pi * t),
      mul_nonneg (norm_nonneg (f t))
        (sub_nonneg.mpr (mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 2 * Real.pi * t)))]
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Eventually.of_forall hmeas) (absolute_convergence f hf z hz) hdmeas
    hbound hB (Eventually.of_forall (fun t w _ => kernel_derivative f t w))
  exact hd.2.differentiableAt.differentiableWithinAt

/-- The positive-sign integral transform is symmetric under the bilinear pairing. -/
lemma integral_inverse_fourier_mul (u v : ℝ → ℂ) (hu : Integrable u) (hv : Integrable v) :
    (∫ x : ℝ, (𝓕⁻ u) x * v x) = ∫ t : ℝ, u t * (𝓕⁻ v) t := by
  have hflip : (-(innerₗ ℝ)).flip = -(innerₗ ℝ) := by
    ext; simp
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := -(innerₗ ℝ)) Real.continuous_fourierChar
    (by change Continuous (fun p : ℝ × ℝ => -(p.2 * p.1)); fun_prop) hu hv
  rw [hflip] at h
  exact h

/-- Agreement of the L² and integral inverse transforms on L¹ ∩ L².
This is proved through their action on genuine Schwartz tests. -/
lemma inverse_fourier_L2_eq_integral (f : ℝ → ℂ) (hf : MemLp f 2 volume)
    (hfi : Integrable f) :
    ((𝓕⁻ (hf.toLp f) : BoundaryL2) : ℝ → ℂ) =ᵐ[volume] (𝓕⁻ f) := by
  have hc : Continuous (𝓕⁻ f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (L := -(innerₗ ℝ))
      (by change Continuous (fun p : ℝ × ℝ => -(p.2 * p.1)); fun_prop) hfi
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕⁻ (hf.toLp f) : BoundaryL2)).locallyIntegrable (by norm_num))
    hc.locallyIntegrable
  intro g hg hgc
  let φ : SchwartzMap ℝ ℂ :=
    (hgc.comp_left (show (Complex.ofRealCLM : ℝ → ℂ) 0 = 0 by rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hg)
  have hp := congrArg (fun u : TemperedDistribution ℝ ℂ => u φ)
    (Lp.fourierInv_toTemperedDistribution_eq (hf.toLp f))
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply,
    smul_eq_mul] at hp
  calc
    (∫ x : ℝ, g x • (𝓕⁻ (hf.toLp f) : BoundaryL2) x) =
        ∫ x : ℝ, φ x * (𝓕⁻ (hf.toLp f) : BoundaryL2) x := by rfl
    _ = ∫ x : ℝ, (𝓕⁻ φ) x * (hf.toLp f) x := hp.symm
    _ = ∫ x : ℝ, (𝓕⁻ φ) x * f x := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ x : ℝ, φ x * (𝓕⁻ f) x := by
      simpa only [SchwartzMap.fourierInv_coe] using
        integral_inverse_fourier_mul φ f φ.integrable hfi
    _ = ∫ x : ℝ, g x • (𝓕⁻ f) x := by rfl
  rfl

lemma extended_memLp (f : ℝ → ℂ) (hf : MemLp f 2 positiveMeasure) :
    MemLp ((Ioi 0).indicator f) 2 volume :=
  (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).mpr hf

def density (f : ℝ → ℂ) (hf : MemLp f 2 positiveMeasure) (y : ℝ) : BoundaryL2 :=
  (extended_memLp (damp f (max y 0))
    (damping_bound f hf (max y 0) (le_max_right _ _)).1).toLp
      ((Ioi 0).indicator (damp f (max y 0)))

def frequencyDensity (f : ℝ → ℂ) (hf : MemLp f 2 positiveMeasure) : BoundaryL2 :=
  (extended_memLp f hf).toLp ((Ioi 0).indicator f)

lemma density_coe (f : ℝ → ℂ) (hf : MemLp f 2 positiveMeasure) {y : ℝ} (hy : 0 ≤ y) :
    (density f hf y : ℝ → ℂ) =ᵐ[volume] (Ioi 0).indicator (damp f y) := by
  simpa only [density, max_eq_left hy] using
    (extended_memLp (damp f (max y 0))
      (damping_bound f hf (max y 0) (le_max_right _ _)).1).coeFn_toLp

lemma density_tendsto (f : ℝ → ℂ) (hf : MemLp f 2 positiveMeasure) :
    Tendsto (density f hf) (𝓝[>] 0) (𝓝 (frequencyDensity f hf)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm (density f hf)
    ((Ioi 0).indicator f) (extended_memLp f hf)).mpr
  apply (damping_convergence f hf).congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict (μ := (volume : Measure ℝ))
    measurableSet_Ioi.nullMeasurableSet]
  apply eLpNorm_congr_ae
  filter_upwards [density_coe f hf (le_of_lt hy)] with t ht
  simp only [Pi.sub_apply, ht]
  exact congrFun (Set.indicator_sub (Ioi (0 : ℝ)) (damp f y) f) t

lemma kernel_slice (x y t : ℝ) :
    kernel ((x : ℂ) + (y : ℂ) * Complex.I) t =
      Complex.exp (((2 * Real.pi * (t * x) : ℝ) : ℂ) * Complex.I) *
        (Real.exp (-2 * Real.pi * y * t) : ℂ) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  unfold kernel
  congr 1
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma inverse_fourier_damp (f : ℝ → ℂ) (x y : ℝ) :
    (𝓕⁻ ((Ioi 0).indicator (damp f y))) x = slice (laplace f) y x := by
  rw [Real.fourierInv_eq']
  simp only [RCLike.inner_apply, conj_trivial] 
  change (∫ t : ℝ, Complex.exp (((2 * Real.pi * (x * t) : ℝ) : ℂ) * Complex.I) •
    (Ioi 0).indicator (damp f y) t) = laplace f ((x : ℂ) + (y : ℂ) * Complex.I)
  rw [laplace, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · simp only [Set.indicator_of_mem ht, smul_eq_mul, kernel_slice, damp]
    rw [mul_comm x t]
    ring
  · simp [ht]

lemma damp_integrable (f : ℝ → ℂ) (hf : MemLp f 2 positiveMeasure)
    {y : ℝ} (hy : 0 < y) : Integrable (damp f y) positiveMeasure := by
  have hi := (absolute_convergence f hf ((y : ℂ) * Complex.I) (by
    simpa [upperHalfPlane])).norm
  apply hi.mono' (damp_measurable f hf y)
  filter_upwards [] with t
  simp only [damp, norm_mul, norm_kernel, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
  exact le_rfl

lemma density_slice (f : ℝ → ℂ) (hf : MemLp f 2 positiveMeasure) {y : ℝ} (hy : 0 < y) :
    ((𝓕⁻ (density f hf y) : BoundaryL2) : ℝ → ℂ) =ᵐ[volume] slice (laplace f) y := by
  have hmem := extended_memLp (damp f y) (damping_bound f hf y hy.le).1
  have hint : Integrable ((Ioi 0).indicator (damp f y)) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr (damp_integrable f hf hy)
  have heq : density f hf y = hmem.toLp ((Ioi 0).indicator (damp f y)) := by
    apply Lp.ext
    exact (density_coe f hf hy.le).trans hmem.coeFn_toLp.symm
  rw [heq]
  exact (inverse_fourier_L2_eq_integral _ hmem hint).trans
    (Eventually.of_forall (fun x => inverse_fourier_damp f x y))

lemma norm_inverse_fourier (u : BoundaryL2) : ‖(𝓕⁻ u : BoundaryL2)‖ = ‖u‖ :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map u

lemma density_norm (f : ℝ → ℂ) (hf : MemLp f 2 positiveMeasure) {y : ℝ} (hy : 0 ≤ y) :
    ‖density f hf y‖ = (eLpNorm (damp f y) 2 positiveMeasure).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (density_coe f hf hy),
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioi.nullMeasurableSet]

lemma slice_memLp (f : ℝ → ℂ) (hf : MemLp f 2 positiveMeasure) {y : ℝ} (hy : 0 < y) :
    MemLp (slice (laplace f) y) 2 volume :=
  (Lp.memLp (𝓕⁻ (density f hf y) : BoundaryL2)).ae_eq (density_slice f hf hy)

lemma slice_laplace_norm (f : ℝ → ℂ) (hf : MemLp f 2 positiveMeasure) {y : ℝ} (hy : 0 < y) :
    ‖(slice_memLp f hf hy).toLp (slice (laplace f) y)‖ =
      (eLpNorm (damp f y) 2 positiveMeasure).toReal := by
  have heq : (slice_memLp f hf hy).toLp (slice (laplace f) y) =
      (𝓕⁻ (density f hf y) : BoundaryL2) := by
    apply Lp.ext
    exact (slice_memLp f hf hy).coeFn_toLp.trans (density_slice f hf hy).symm
  rw [heq, norm_inverse_fourier, density_norm f hf hy.le]

lemma slice_of_represents {F : ℂ → ℂ} {f : ℝ → ℂ} (hF : Represents F f) {y : ℝ} (hy : 0 < y) :
    slice F y = slice (laplace f) y := by
  funext x
  exact hF.2 _ (by simpa [upperHalfPlane] using hy)

theorem horizontal_norm : HorizontalNorm := by
  intro F f hF y hy
  rw [slice_of_represents hF hy]
  exact ⟨slice_memLp f hF.1 hy, slice_laplace_norm f hF.1 hy⟩

lemma laplace_hasBoundary (f : ℝ → ℂ) (hf : MemLp f 2 positiveMeasure) :
    HasBoundary (laplace f) (𝓕⁻ (frequencyDensity f hf)) := by
  refine ⟨fun y => 𝓕⁻ (density f hf y), fun y hy => density_slice f hf hy, ?_⟩
  exact (FourierTransform.continuous_fourierInv.tendsto (frequencyDensity f hf)).comp (density_tendsto f hf)

theorem boundary_fourier : BoundaryFourier := by
  intro F f hF
  refine ⟨𝓕⁻ (frequencyDensity f hF.1), ?_, ?_⟩
  · obtain ⟨s, hs, hlim⟩ := laplace_hasBoundary f hF.1
    refine ⟨s, ?_, hlim⟩
    intro y hy
    rw [slice_of_represents hF hy]
    exact hs y hy
  · rw [FourierTransform.fourier_fourierInv_eq]
    exact (extended_memLp f hF.1).coeFn_toLp

lemma boundary_unique {F : ℂ → ℂ} {b c : BoundaryL2}
    (hb : HasBoundary F b) (hc : HasBoundary F c) : b = c := by
  obtain ⟨s, hs, hsb⟩ := hb
  obtain ⟨t, ht, htc⟩ := hc
  have heq : s =ᶠ[𝓝[>] (0 : ℝ)] t := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    apply Lp.ext
    exact (hs y hy).trans (ht y hy).symm
  exact tendsto_nhds_unique hsb (htc.congr' heq.symm)

theorem representation_unique : RepresentationUnique := by
  intro F f g hF hG
  obtain ⟨b, hb, hbf⟩ := boundary_fourier F f hF
  obtain ⟨c, hc, hcg⟩ := boundary_fourier F g hG
  have hbc : b = c := boundary_unique hb hc
  subst c
  have hfg := hbf.symm.trans hcg
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards [hfg] with t ht hmem
  simpa only [Set.indicator_of_mem hmem] using ht

lemma integral_norm_sq_eq {μ : Measure ℝ} (u : ℝ → ℂ) (hu : MemLp u 2 μ) :
    (∫ t : ℝ, ‖u t‖ ^ 2 ∂μ) = ‖hu.toLp u‖ ^ 2 := by
  calc
    (∫ t : ℝ, ‖u t‖ ^ 2 ∂μ) = ∫ t : ℝ, ‖hu.toLp u t‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hu.coeFn_toLp] with t ht
      rw [ht]
    _ = inner ℝ (hu.toLp u) (hu.toLp u) := by
      rw [L2.inner_def]
      simp only [real_inner_self_eq_norm_sq]
    _ = ‖hu.toLp u‖ ^ 2 := real_inner_self_eq_norm_sq _

/-- The entire forward implication, including the actual square-integral bound. -/
theorem laplace_isH2 (f : ℝ → ℂ) (hf : MemLp f 2 positiveMeasure) : IsH2 (laplace f) := by
  refine ⟨laplace_differentiableOn f hf, ‖hf.toLp f‖ ^ 2, sq_nonneg _, ?_⟩
  intro y hy
  refine ⟨slice_memLp f hf hy, ?_⟩
  rw [integral_norm_sq_eq _ (slice_memLp f hf hy), slice_laplace_norm f hf hy,
    Lp.norm_toLp]
  have hle := ENNReal.toReal_mono hf.eLpNorm_ne_top (damping_bound f hf y hy.le).2
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg hle 2

/-- Any represented function is Hardy, independently of its values outside the domain. -/
theorem represents_isH2 {F : ℂ → ℂ} {f : ℝ → ℂ} (hF : Represents F f) : IsH2 F := by
  obtain ⟨hd, C, hC, hb⟩ := laplace_isH2 f hF.1
  refine ⟨hd.congr (fun z hz => hF.2 z hz), C, hC, ?_⟩
  intro y hy
  rw [slice_of_represents hF hy]
  exact hb y hy

theorem representation_forward : RepresentationForward := by
  intro F f hF
  exact represents_isH2 hF

theorem boundary_of_representation : BoundaryOfRepresentation := by
  intro F f hF
  obtain ⟨b, hb, _⟩ := boundary_fourier F f hF
  exact ⟨b, hb, fun c hc => boundary_unique hc hb⟩

lemma slice_continuous {F : ℂ → ℂ} (hF : IsH2 F) {y : ℝ} (hy : 0 < y) :
    Continuous (slice F y) := by
  apply hF.1.continuousOn.comp_continuous (by fun_prop)
  intro x
  simpa [upperHalfPlane] using hy

/-- Final pointwise reconstruction from a causal spectral family. The missing
converse need only construct this family; no integral-identification or boundary
hypothesis is imposed on it. -/
lemma represents_of_spectral_slices {F : ℂ → ℂ} (hF : IsH2 F)
    (f : ℝ → ℂ) (hf : MemLp f 2 positiveMeasure)
    (hs : ∀ y : ℝ, 0 < y → ∃ d : BoundaryL2,
      (d : ℝ → ℂ) =ᵐ[volume] (Ioi 0).indicator (damp f y) ∧
      ((𝓕⁻ d : BoundaryL2) : ℝ → ℂ) =ᵐ[volume] slice F y) :
    Represents F f := by
  refine ⟨hf, ?_⟩
  intro z hz
  obtain ⟨d, hd, hds⟩ := hs z.im hz
  have heq : d = density f hf z.im := by
    apply Lp.ext
    exact hd.trans (density_coe f hf (le_of_lt hz)).symm
  rw [heq] at hds
  have hae := hds.symm.trans (density_slice f hf hz)
  have hslice : slice F z.im = slice (laplace f) z.im :=
    (volume : Measure ℝ).eq_of_ae_eq hae (slice_continuous hF hz)
      (slice_continuous (laplace_isH2 f hf) hz)
  have hpoint := congrFun hslice z.re
  simpa only [slice, Complex.re_add_im] using hpoint

/-- Exponential transport determines one common, initially unweighted density.
Only the relation to the height-one slice is needed. -/
lemma common_density_of_transport (d : ℝ → BoundaryL2)
    (ht : ∀ y : ℝ, 0 < y →
      (d y : ℝ → ℂ) =ᵐ[volume] damp (d 1) (y - 1)) :
    ∃ g : ℝ → ℂ, AEStronglyMeasurable g volume ∧
      ∀ y : ℝ, 0 < y → (d y : ℝ → ℂ) =ᵐ[volume] damp g y := by
  let g : ℝ → ℂ := fun t => (Real.exp (2 * Real.pi * t) : ℂ) * d 1 t
  refine ⟨g, ?_, ?_⟩
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      (Real.exp (2 * Real.pi * t) : ℂ))).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable (d 1))
  · intro y hy
    apply (ht y hy).trans
    apply Eventually.of_forall
    intro t
    dsimp [g, damp]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring

/-- Fatou as the height tends to zero makes the common density globally L².
There is no boundary function among the hypotheses. -/
lemma common_density_memLp (g : ℝ → ℂ) (hg : AEStronglyMeasurable g volume)
    (C : ℝ≥0) (hb : ∀ y : ℝ, 0 < y → eLpNorm (damp g y) 2 volume ≤ C) :
    MemLp g 2 volume ∧ eLpNorm g 2 volume ≤ C := by
  have hm (y : ℝ) : AEStronglyMeasurable (damp g y) volume :=
    (by fun_prop : Continuous (fun t : ℝ =>
      (Real.exp (-2 * Real.pi * y * t) : ℂ))).aestronglyMeasurable.mul hg
  have ht : ∀ᵐ t : ℝ, Tendsto (fun y : ℝ => damp g y t)
      (𝓝[>] 0) (𝓝 (g t)) := by
    apply Eventually.of_forall
    intro t
    have hc : Continuous (fun y : ℝ => damp g y t) := by unfold damp; fun_prop
    simpa [damp] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hle : eLpNorm g 2 volume ≤ C := by
    apply Lp.eLpNorm_le_of_ae_tendsto _ hm hg ht
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hb y hy
  exact ⟨hle.trans_lt ENNReal.coe_lt_top, hle⟩

/-- Uniformly bounded exponential dampings force the density to vanish at
negative frequencies. Fatou supplies an a.e. finite liminf, contradicting the
exponential growth at any negative frequency with nonzero density. -/
lemma common_density_causal (g : ℝ → ℂ) (C : ℝ≥0)
    (hb : ∀ y : ℝ, 0 < y → eLpNorm (damp g y) 2 volume ≤ C) :
    ∀ᵐ t : ℝ, t < 0 → g t = 0 := by
  have hfin := ae_bdd_liminf_atTop_of_eLpNorm_bdd
    (μ := (volume : Measure ℝ)) (p := (2 : ℝ≥0∞)) (by norm_num)
    (f := fun n : ℕ => damp g ((n : ℝ) + 1))
    (fun n => hb _ (by positivity))
  filter_upwards [hfin] with t ht hneg
  by_contra hne
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).atTop_add tendsto_const_nhds
  have ha : 0 < -2 * Real.pi * t := by
    nlinarith [Real.pi_pos]
  have he : Tendsto (fun n : ℕ => Real.exp (-2 * Real.pi *
      ((n : ℝ) + 1) * t)) atTop atTop := by
    convert Real.tendsto_exp_atTop.comp (hn.const_mul_atTop ha) using 1
    ext n
    congr 1
    ring
  have hnorm : Tendsto (fun n : ℕ => ‖damp g ((n : ℝ) + 1) t‖)
      atTop atTop := by
    simpa only [damp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] using he.atTop_mul_const (norm_pos_iff.mpr hne)
  have hinfty : Tendsto (fun n : ℕ => ‖damp g ((n : ℝ) + 1) t‖ₑ)
      atTop (𝓝 ∞) := by
    simpa only [Function.comp_def, ofReal_norm] using ENNReal.tendsto_ofReal_atTop.comp hnorm
  rw [hinfty.liminf_eq] at ht
  exact (lt_irrefl _ ht)

/-- Causal reconstruction from a uniformly bounded exponential spectral family.
The analytic work needed for the converse is precisely to construct a family
with the transport relation; no such construction is assumed for Hardy functions
in any theorem here. -/
lemma causal_reconstruction (d : ℝ → BoundaryL2) (C : ℝ≥0)
    (hb : ∀ y : ℝ, 0 < y → eLpNorm (d y) 2 volume ≤ C)
    (ht : ∀ y : ℝ, 0 < y →
      (d y : ℝ → ℂ) =ᵐ[volume] damp (d 1) (y - 1)) :
    ∃ f : ℝ → ℂ, MemLp f 2 positiveMeasure ∧
      ∀ y : ℝ, 0 < y →
        (d y : ℝ → ℂ) =ᵐ[volume] (Ioi 0).indicator (damp f y) := by
  obtain ⟨g, hg, hgd⟩ := common_density_of_transport d ht
  have hgb (y : ℝ) (hy : 0 < y) : eLpNorm (damp g y) 2 volume ≤ C := by
    rw [← eLpNorm_congr_ae (hgd y hy)]
    exact hb y hy
  have hgm := (common_density_memLp g hg C hgb).1
  have hgc := common_density_causal g C hgb
  refine ⟨g, hgm.restrict (Ioi 0), ?_⟩
  intro y hy
  apply (hgd y hy).trans
  filter_upwards [hgc, (volume : Measure ℝ).ae_ne 0] with t ht ht0
  by_cases hpos : t ∈ Ioi (0 : ℝ)
  · exact (Set.indicator_of_mem hpos _).symm
  · have hneg : t < 0 := lt_of_le_of_ne (not_lt.mp hpos) ht0
    simp only [Set.indicator_of_notMem hpos, damp, ht hneg, mul_zero]

/-- Assemble the converse once analytic exponential transport has been obtained.
This conditional lemma records the exact remaining analytic interface. -/
lemma represents_of_transport {F : ℂ → ℂ} (hF : IsH2 F)
    (d : ℝ → BoundaryL2) (C : ℝ≥0)
    (hb : ∀ y : ℝ, 0 < y → eLpNorm (d y) 2 volume ≤ C)
    (ht : ∀ y : ℝ, 0 < y →
      (d y : ℝ → ℂ) =ᵐ[volume] damp (d 1) (y - 1))
    (hs : ∀ y : ℝ, 0 < y →
      ((𝓕⁻ (d y) : BoundaryL2) : ℝ → ℂ) =ᵐ[volume] slice F y) :
    ∃ f : ℝ → ℂ, Represents F f := by
  obtain ⟨f, hf, hfd⟩ := causal_reconstruction d C hb ht
  refine ⟨f, represents_of_spectral_slices hF f hf ?_⟩
  intro y hy
  exact ⟨d y, hfd y hy, hs y hy⟩

/-- The Fourier integral on a bounded horizontal segment. -/
def truncatedFourier (u : ℝ → ℂ) (l r t : ℝ) : ℂ :=
  ∫ x : ℝ in l..r, Complex.exp (((-2 * Real.pi * (t * x) : ℝ) : ℂ) * Complex.I) * u x

/-- The corresponding vertical edge in a Fourier contour shift. -/
def verticalFourier (F : ℂ → ℂ) (a b x t : ℝ) : ℂ :=
  ∫ y : ℝ in a..b, kernel ((x : ℂ) + (y : ℂ) * Complex.I) (-t) *
    F ((x : ℂ) + (y : ℂ) * Complex.I)

lemma weighted_horizontal_integral (F : ℂ → ℂ) (a l r t : ℝ) :
    (∫ x : ℝ in l..r, kernel ((x : ℂ) + (a : ℂ) * Complex.I) (-t) *
      F ((x : ℂ) + (a : ℂ) * Complex.I)) =
    (Real.exp (2 * Real.pi * a * t) : ℂ) * truncatedFourier (slice F a) l r t := by
  rw [truncatedFourier, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [kernel_slice]
  simp only [neg_mul, mul_neg, neg_neg, slice]
  ring

/-- Cauchy-Goursat gives the exact finite-contour identity used in transport. -/
lemma fourier_rectangle {F : ℂ → ℂ} (hF : IsH2 F) (a b l r t : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    (Real.exp (2 * Real.pi * a * t) : ℂ) * truncatedFourier (slice F a) l r t -
      (Real.exp (2 * Real.pi * b * t) : ℂ) * truncatedFourier (slice F b) l r t +
      Complex.I * verticalFourier F a b r t -
      Complex.I * verticalFourier F a b l t = 0 := by
  let G : ℂ → ℂ := fun z => kernel z (-t) * F z
  have hg : DifferentiableOn ℂ G upperHalfPlane := by
    apply DifferentiableOn.mul _ hF.1
    unfold kernel
    fun_prop
  have hrect : DifferentiableOn ℂ G
      (Set.uIcc ((l : ℂ) + (a : ℂ) * Complex.I).re
        ((r : ℂ) + (b : ℂ) * Complex.I).re ×ℂ
       Set.uIcc ((l : ℂ) + (a : ℂ) * Complex.I).im
        ((r : ℂ) + (b : ℂ) * Complex.I).im) := by
    apply hg.mono
    intro z hz
    have him : z.im ∈ Set.uIcc a b := by simpa using hz.2
    change 0 < z.im
    exact (lt_min ha hb).trans_le him.1
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G
    ((l : ℂ) + (a : ℂ) * Complex.I) ((r : ℂ) + (b : ℂ) * Complex.I) hrect
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, zero_add, smul_eq_mul] at h
  simpa only [G, weighted_horizontal_integral, verticalFourier] using h

lemma exists_ge_norm_lt_of_integrable {A : ℝ → ℝ} (hA : Integrable A)
    (b ε : ℝ) (hε : 0 < ε) : ∃ x : ℝ, b ≤ x ∧ ‖A x‖ < ε := by
  by_contra h
  push Not at h
  have hi : Integrable (fun _ : ℝ => ε) (volume.restrict (Ici b)) := by
    apply hA.restrict.norm.mono' aestronglyMeasurable_const
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    simpa only [Real.norm_eq_abs, abs_of_pos hε] using h x hx
  have hf := (integrable_const_iff_isFiniteMeasure (ne_of_gt hε)).mp hi
  have hh := hf.measure_univ_lt_top
  simpa using hh

lemma integrable_exists_endpoints {A : ℝ → ℝ} (hA : Integrable A) :
    ∃ l r : ℕ → ℝ, Tendsto l atTop atBot ∧ Tendsto r atTop atTop ∧
      Tendsto (fun n => A (l n)) atTop (𝓝 0) ∧
      Tendsto (fun n => A (r n)) atTop (𝓝 0) ∧ (∀ n, l n ≤ r n) := by
  have hpos (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  choose r hr hAr using fun n : ℕ => exists_ge_norm_lt_of_integrable hA n (1 / ((n : ℝ) + 1)) (hpos n)
  have hr_top : Tendsto r atTop atTop := tendsto_atTop_mono hr tendsto_natCast_atTop_atTop
  have hAr_lim : Tendsto (fun n => A (r n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => (hAr n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have hAn : Integrable (fun x : ℝ => A (-x)) := by
    exact ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp hA.aestronglyMeasurable).mpr hA
  choose l hl hAl using fun n : ℕ => exists_ge_norm_lt_of_integrable hAn n (1 / ((n : ℝ) + 1)) (hpos n)
  refine ⟨fun n => -l n, r, ?_, hr_top, ?_, hAr_lim, ?_⟩
  · exact tendsto_neg_atTop_atBot.comp (tendsto_atTop_mono hl tendsto_natCast_atTop_atTop)
  · apply squeeze_zero_norm (fun n => (hAl n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n
    exact (neg_nonpos.mpr ((Nat.cast_nonneg n).trans (hl n))).trans
      ((Nat.cast_nonneg n).trans (hr n))

lemma integral_fourier_mul (u v : ℝ → ℂ) (hu : Integrable u) (hv : Integrable v) :
    (∫ x : ℝ, (𝓕 u) x * v x) = ∫ t : ℝ, u t * (𝓕 v) t := by
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
    ext; simp
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ ℝ) Real.continuous_fourierChar
    (by change Continuous (fun p : ℝ × ℝ => p.2 * p.1); fun_prop) hu hv
  rw [hflip] at h
  exact h

lemma fourier_L2_eq_integral (f : ℝ → ℂ) (hf : MemLp f 2 volume)
    (hfi : Integrable f) :
    ((𝓕 (hf.toLp f) : BoundaryL2) : ℝ → ℂ) =ᵐ[volume] (𝓕 f) := by
  have hc : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (L := innerₗ ℝ)
      (by change Continuous (fun p : ℝ × ℝ => p.2 * p.1); fun_prop) hfi
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 (hf.toLp f) : BoundaryL2)).locallyIntegrable (by norm_num))
    hc.locallyIntegrable
  intro g hg hgc
  let φ : SchwartzMap ℝ ℂ :=
    (hgc.comp_left (show (Complex.ofRealCLM : ℝ → ℂ) 0 = 0 by rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hg)
  have hp := congrArg (fun u : TemperedDistribution ℝ ℂ => u φ)
    (Lp.fourier_toTemperedDistribution_eq (hf.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
    smul_eq_mul] at hp
  calc
    (∫ x : ℝ, g x • (𝓕 (hf.toLp f) : BoundaryL2) x) =
        ∫ x : ℝ, φ x * (𝓕 (hf.toLp f) : BoundaryL2) x := by rfl
    _ = ∫ x : ℝ, (𝓕 φ) x * (hf.toLp f) x := hp.symm
    _ = ∫ x : ℝ, (𝓕 φ) x * f x := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ x : ℝ, φ x * (𝓕 f) x := by
      simpa only [SchwartzMap.fourier_coe] using
        integral_fourier_mul φ f φ.integrable hfi
    _ = ∫ x : ℝ, g x • (𝓕 f) x := by rfl
  rfl

lemma indicator_Ioc_integrable (u : ℝ → ℂ) (hu : MemLp u 2 volume) (l r : ℝ) :
    Integrable ((Ioc l r).indicator u) := by
  rw [integrable_indicator_iff measurableSet_Ioc]
  exact (hu.restrict (Ioc l r)).integrable (by norm_num)

lemma fourier_indicator_Ioc (u : ℝ → ℂ) (l r t : ℝ) (hlr : l ≤ r) :
    (𝓕 ((Ioc l r).indicator u)) t = truncatedFourier u l r t := by
  rw [Real.fourier_real_eq_integral_exp_smul, truncatedFourier,
    intervalIntegral.integral_of_le hlr, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Ioc l r
  · simp only [Set.indicator_of_mem hx, smul_eq_mul]
    congr 3
    ring
  · simp [hx]


lemma indicator_Ioc_tendsto_L2 (u : ℝ → ℂ) (hu : MemLp u 2 volume)
    (l r : ℕ → ℝ) (hl : Tendsto l atTop atBot) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n => (hu.indicator measurableSet_Ioc.nullMeasurableSet).toLp
      ((Ioc (l n) (r n)).indicator u)) atTop (𝓝 (hu.toLp u)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr
  have hmeas (n : ℕ) : AEStronglyMeasurable
      ((Ioc (l n) (r n)).indicator u - u) volume :=
    (hu.aestronglyMeasurable.indicator measurableSet_Ioc).sub hu.aestronglyMeasurable
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ x ∂volume,
      ‖((Ioc (l n) (r n)).indicator u - u) x‖ₑ ^ (2 : ℝ) ≤ ‖u x‖ₑ ^ (2 : ℝ) := by
    filter_upwards [] with n
    filter_upwards [] with x
    by_cases hx : x ∈ Ioc (l n) (r n)
    · simp [hx]
    · simp [hx]
  have hfin : (∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂volume) ≠ ∞ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num) hu).ne
  have hlim : ∀ᵐ x ∂volume,
      Tendsto (fun n : ℕ => ‖((Ioc (l n) (r n)).indicator u - u) x‖ₑ ^ (2 : ℝ))
        atTop (𝓝 0) := by
    filter_upwards [] with x
    apply tendsto_const_nhds.congr'
    filter_upwards [hl.eventually (eventually_lt_atBot x),
      hr.eventually (eventually_ge_atTop x)] with n hn₁ hn₂
    simp [show x ∈ Ioc (l n) (r n) from ⟨hn₁, hn₂⟩]
  have hI : Tendsto (fun n : ℕ =>
      ∫⁻ x, ‖((Ioc (l n) (r n)).indicator u - u) x‖ₑ ^ (2 : ℝ) ∂volume)
        atTop (𝓝 0) := by
    simpa using tendsto_lintegral_filter_of_dominated_convergence'
      (fun x => ‖u x‖ₑ ^ (2 : ℝ))
      (Eventually.of_forall (fun n => (hmeas n).enorm.pow_const _)) hbound hfin hlim
  have hpow := (ENNReal.continuous_rpow_const (y := (1 / (2 : ℝ)))).continuousAt.tendsto.comp hI
  simpa only [Function.comp_def, eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num) (hmeas _), ENNReal.toReal_ofNat,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using hpow


lemma truncatedFourier_subsequence (u : ℝ → ℂ) (hu : MemLp u 2 volume)
    (l r : ℕ → ℝ) (hl : Tendsto l atTop atBot) (hr : Tendsto r atTop atTop)
    (hlr : ∀ n, l n ≤ r n) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ᵐ t ∂volume,
      Tendsto (fun n => truncatedFourier u (l (k n)) (r (k n)) t) atTop
        (𝓝 ((𝓕 (hu.toLp u) : BoundaryL2) t)) := by
  have hd := (FourierTransform.continuous_fourier (E := BoundaryL2)).continuousAt.tendsto.comp
    (indicator_Ioc_tendsto_L2 u hu l r hl hr)
  obtain ⟨k, hk, hkae⟩ := (tendstoInMeasure_of_tendsto_Lp hd).exists_seq_tendsto_ae
  have heq : ∀ᵐ t ∂volume, ∀ n : ℕ,
      (𝓕 ((hu.indicator measurableSet_Ioc.nullMeasurableSet).toLp
        ((Ioc (l n) (r n)).indicator u)) : BoundaryL2) t =
          truncatedFourier u (l n) (r n) t := by
    rw [ae_all_iff]
    intro n
    exact (fourier_L2_eq_integral _ (hu.indicator measurableSet_Ioc.nullMeasurableSet)
      (indicator_Ioc_integrable u hu (l n) (r n))).trans
        (Eventually.of_forall fun t => fourier_indicator_Ioc u (l n) (r n) t (hlr n))
  refine ⟨k, hk, ?_⟩
  filter_upwards [hkae, heq] with t ht heq
  simpa only [Function.comp_apply, heq] using ht


lemma spectral_family_basic {F : ℂ → ℂ} (hF : IsH2 F) :
    ∃ d : ℝ → BoundaryL2, ∃ C : ℝ≥0,
      (∀ y : ℝ, 0 < y → eLpNorm (d y) 2 volume ≤ C) ∧
      (∀ y : ℝ, 0 < y → ((𝓕⁻ (d y) : BoundaryL2) : ℝ → ℂ) =ᵐ[volume] slice F y) ∧
      (∀ y : ℝ, ∀ hy : 0 < y, d y = 𝓕 ((hF.2.choose_spec.2 y hy).1.toLp (slice F y))) := by
  let s : ℝ → BoundaryL2 := fun y =>
    if hy : 0 < y then (hF.2.choose_spec.2 y hy).1.toLp (slice F y) else 0
  let d : ℝ → BoundaryL2 := fun y => 𝓕 (s y)
  obtain ⟨B, hB, hb⟩ := hF.2
  refine ⟨d, ⟨Real.sqrt B, Real.sqrt_nonneg B⟩, ?_, ?_, ?_⟩
  · intro y hy
    have hs : s y = (hb y hy).1.toLp (slice F y) := by simp only [s, dite_eq_left hy]
    have hh : ‖s y‖ ^ 2 ≤ B := by
      rw [hs, ← integral_norm_sq_eq]
      exact (hb y hy).2
    have hn : ‖d y‖ ≤ Real.sqrt B := by
      change ‖𝓕 (s y)‖ ≤ Real.sqrt B
      rw [Lp.norm_fourier_eq]
      exact (Real.le_sqrt (norm_nonneg _) hB).mpr hh
    rw [← Lp.enorm_def]
    apply enorm_le_coe.mpr
    exact_mod_cast hn
  · intro y hy
    have hs : s y = (hb y hy).1.toLp (slice F y) := by simp only [s, dite_eq_left hy]
    simpa only [d, FourierTransform.fourierInv_fourier_eq, hs] using (hb y hy).1.coeFn_toLp
  · intro y hy
    simp only [d, s, dite_eq_left hy]


lemma exponential_cancel (a b t : ℝ) (A B : ℂ)
    (h : (Real.exp (2 * Real.pi * a * t) : ℂ) * A =
      (Real.exp (2 * Real.pi * b * t) : ℂ) * B) :
    A = (Real.exp (-2 * Real.pi * (a - b) * t) : ℂ) * B := by
  have he : (Real.exp (-2 * Real.pi * a * t) : ℂ) *
      (Real.exp (2 * Real.pi * a * t) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    have hz : -2 * Real.pi * a * t + 2 * Real.pi * a * t = 0 := by ring
    rw [hz, Real.exp_zero, Complex.ofReal_one]
  calc
    A = (Real.exp (-2 * Real.pi * a * t) : ℂ) *
        ((Real.exp (2 * Real.pi * a * t) : ℂ) * A) := by rw [← mul_assoc, he, one_mul]
    _ = (Real.exp (-2 * Real.pi * a * t) : ℂ) *
        ((Real.exp (2 * Real.pi * b * t) : ℂ) * B) := by rw [h]
    _ = (Real.exp (-2 * Real.pi * (a - b) * t) : ℂ) * B := by
      rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      ring

lemma transport_of_contour_limits {F : ℂ → ℂ} (hF : IsH2 F)
    (a b t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (l r : ℕ → ℝ) (A B : ℂ)
    (hA : Tendsto (fun n => truncatedFourier (slice F a) (l n) (r n) t) atTop (𝓝 A))
    (hB : Tendsto (fun n => truncatedFourier (slice F b) (l n) (r n) t) atTop (𝓝 B))
    (hv : Tendsto (fun n => verticalFourier F a b (r n) t -
        verticalFourier F a b (l n) t) atTop (𝓝 0)) :
    A = (Real.exp (-2 * Real.pi * (a - b) * t) : ℂ) * B := by
  have hz : Tendsto (fun n =>
      (Real.exp (2 * Real.pi * a * t) : ℂ) *
        truncatedFourier (slice F a) (l n) (r n) t -
      (Real.exp (2 * Real.pi * b * t) : ℂ) *
        truncatedFourier (slice F b) (l n) (r n) t +
      Complex.I * (verticalFourier F a b (r n) t - verticalFourier F a b (l n) t))
      atTop (𝓝 ((Real.exp (2 * Real.pi * a * t) : ℂ) * A -
        (Real.exp (2 * Real.pi * b * t) : ℂ) * B)) := by
    convert ((hA.const_mul _).sub (hB.const_mul _)).add (hv.const_mul Complex.I) using 1
    simp only [mul_zero, add_zero]
  have he : (Real.exp (2 * Real.pi * a * t) : ℂ) * A -
        (Real.exp (2 * Real.pi * b * t) : ℂ) * B = 0 := by
    apply tendsto_nhds_unique hz
    have hc : (fun n =>
      (Real.exp (2 * Real.pi * a * t) : ℂ) *
        truncatedFourier (slice F a) (l n) (r n) t -
      (Real.exp (2 * Real.pi * b * t) : ℂ) *
        truncatedFourier (slice F b) (l n) (r n) t +
      Complex.I * (verticalFourier F a b (r n) t - verticalFourier F a b (l n) t)) =
      fun _ => (0 : ℂ) := by
      funext n
      have hrect := fourier_rectangle hF a b (l n) (r n) t ha hb
      linear_combination hrect
    rw [hc]
    exact tendsto_const_nhds
  exact exponential_cancel a b t A B (sub_eq_zero.mp he)


def stripSquare (F : ℂ → ℂ) (a b x : ℝ) : ℝ :=
  ∫ y : ℝ in Set.uIcc a b, ‖F ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2

lemma stripSquare_integrable {F : ℂ → ℂ} (hF : IsH2 F) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) : Integrable (stripSquare F a b) := by
  let c := min a b
  have hc : 0 < c := lt_min ha hb
  let G : ℝ × ℝ → ℝ := fun p =>
    ‖F ((p.1 : ℂ) + ((max c p.2 : ℝ) : ℂ) * Complex.I)‖ ^ 2
  have hcont : Continuous G := by
    apply Continuous.pow
    apply Continuous.norm
    apply hF.1.continuousOn.comp_continuous (by fun_prop)
    intro p
    simpa [upperHalfPlane] using hc.trans_le (le_max_left c p.2)
  have heq (x y : ℝ) (hy : y ∈ uIcc a b) :
      G (x,y) = ‖slice F y x‖ ^ 2 := by
    dsimp only [G, c, slice]
    rw [max_eq_right hy.1]
  obtain ⟨C, hC, hbound⟩ := hF.2
  let : IsFiniteMeasure (volume.restrict (uIcc a b)) :=
    isFiniteMeasure_restrict.mpr isCompact_uIcc.measure_lt_top.ne
  have hprod : Integrable G (volume.prod (volume.restrict (uIcc a b))) := by
    apply (integrable_prod_iff' hcont.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_uIcc] with y hy
      have hypos : 0 < y := hc.trans_le hy.1
      convert (memLp_two_iff_integrable_sq_norm (hbound y hypos).1.aestronglyMeasurable).mp
        (hbound y hypos).1 using 1
      ext x
      exact heq x y hy
    · apply Integrable.mono' (integrable_const C)
        hcont.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_uIcc] with y hy
      have hypos : 0 < y := hc.trans_le hy.1
      have hnorm (x : ℝ) : ‖G (x,y)‖ = ‖slice F y x‖ ^ 2 := by
        rw [heq x y hy, Real.norm_of_nonneg (sq_nonneg _)]
      simp_rw [hnorm]
      rw [Real.norm_of_nonneg (integral_nonneg (fun x => sq_nonneg _))]
      exact (hbound y hypos).2
  convert hprod.integral_prod_left using 1
  ext x
  apply setIntegral_congr_fun measurableSet_uIcc
  intro y hy
  exact (heq x y hy).symm

lemma verticalFourier_norm_le {F : ℂ → ℂ} (hF : IsH2 F) (a b x t : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    ‖verticalFourier F a b x t‖ ≤
      Real.sqrt (∫ y : ℝ in uIcc a b, (Real.exp (2 * Real.pi * y * t)) ^ 2) *
      Real.sqrt (stripSquare F a b x) := by
  let K : ℝ → ℂ := fun y => kernel ((x : ℂ) + (y : ℂ) * Complex.I) (-t)
  let V : ℝ → ℂ := fun y => F ((x : ℂ) + (y : ℂ) * Complex.I)
  have hK : ContinuousOn K (uIcc a b) := by unfold K kernel; fun_prop
  have hV : ContinuousOn V (uIcc a b) := by
    apply hF.1.continuousOn.comp (by fun_prop)
    intro y hy
    simpa [upperHalfPlane] using (lt_min ha hb).trans_le hy.1
  have hKm : MemLp K 2 (volume.restrict (uIcc a b)) := by
    apply (memLp_two_iff_integrable_sq_norm
      (hK.aestronglyMeasurable measurableSet_uIcc)).mpr
    exact (hK.norm.pow 2).integrableOn_uIcc
  have hVm : MemLp V 2 (volume.restrict (uIcc a b)) := by
    apply (memLp_two_iff_integrable_sq_norm
      (hV.aestronglyMeasurable measurableSet_uIcc)).mpr
    exact (hV.norm.pow 2).integrableOn_uIcc
  have hCS := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hKm) (by simpa using hVm)
  have hn (y : ℝ) : ‖K y‖ = Real.exp (2 * Real.pi * y * t) := by
    simp only [K, norm_kernel, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add]
    congr 1
    ring
  have hCS' : (∫ y : ℝ in uIcc a b, ‖K y‖ * ‖V y‖) ≤
      Real.sqrt (∫ y : ℝ in uIcc a b, (Real.exp (2 * Real.pi * y * t)) ^ 2) *
      Real.sqrt (stripSquare F a b x) := by
    simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, hn, V, stripSquare] using hCS
  apply le_trans (intervalIntegral.norm_integral_le_integral_norm_uIoc) _
  rw [setIntegral_congr_set uIoc_ae_eq_interval]
  simpa only [norm_mul, K, V] using hCS'

lemma verticalFourier_exists_endpoints {F : ℂ → ℂ} (hF : IsH2 F) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    ∃ l r : ℕ → ℝ, Tendsto l atTop atBot ∧ Tendsto r atTop atTop ∧
      (∀ t : ℝ,
        Tendsto (fun n => verticalFourier F a b (l n) t) atTop (𝓝 0) ∧
        Tendsto (fun n => verticalFourier F a b (r n) t) atTop (𝓝 0)) ∧
      (∀ n, l n ≤ r n) := by
  obtain ⟨l, r, hl, hr, hAl, hAr, hlr⟩ :=
    integrable_exists_endpoints (stripSquare_integrable hF a b ha hb)
  refine ⟨l, r, hl, hr, ?_, hlr⟩
  intro t
  have hzero {e : ℕ → ℝ}
      (he : Tendsto (fun n => stripSquare F a b (e n)) atTop (𝓝 0)) :
      Tendsto (fun n => verticalFourier F a b (e n) t) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => verticalFourier_norm_le hF a b (e n) t ha hb)
    simpa only [Real.sqrt_zero, mul_zero, Function.comp_def] using
      (Real.continuous_sqrt.tendsto 0 |>.comp he).const_mul
        (Real.sqrt (∫ y : ℝ in uIcc a b, (Real.exp (2 * Real.pi * y * t)) ^ 2))
  exact ⟨hzero hAl, hzero hAr⟩


lemma spectral_transport_of_edges {F : ℂ → ℂ} (hF : IsH2 F)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (l r : ℕ → ℝ) (hl : Tendsto l atTop atBot) (hr : Tendsto r atTop atTop)
    (hlr : ∀ n, l n ≤ r n)
    (hv : ∀ t : ℝ, Tendsto (fun n => verticalFourier F a b (r n) t -
      verticalFourier F a b (l n) t) atTop (𝓝 0)) :
    ((𝓕 ((hF.2.choose_spec.2 a ha).1.toLp (slice F a)) : BoundaryL2) : ℝ → ℂ) =ᵐ[volume]
      damp (𝓕 ((hF.2.choose_spec.2 b hb).1.toLp (slice F b)) : BoundaryL2) (a - b) := by
  let ua := (hF.2.choose_spec.2 a ha).1
  let ub := (hF.2.choose_spec.2 b hb).1
  obtain ⟨k, hk, hka⟩ := truncatedFourier_subsequence (slice F a) ua l r hl hr hlr
  obtain ⟨j, hj, hjb⟩ := truncatedFourier_subsequence (slice F b) ub
    (fun n => l (k n)) (fun n => r (k n))
    (hl.comp hk.tendsto_atTop) (hr.comp hk.tendsto_atTop) (fun n => hlr (k n))
  filter_upwards [hka, hjb] with t hta htb
  exact transport_of_contour_limits hF a b t ha hb
    (fun n => l (k (j n))) (fun n => r (k (j n))) _ _
    (hta.comp hj.tendsto_atTop) htb ((hv t).comp (hk.tendsto_atTop.comp hj.tendsto_atTop))


/-- Holomorphy transports the L² Fourier densities between every pair of
positive heights. The exceptional set is allowed to depend on the heights. -/
lemma spectral_transport {F : ℂ → ℂ} (hF : IsH2 F)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ((𝓕 ((hF.2.choose_spec.2 a ha).1.toLp (slice F a)) : BoundaryL2) : ℝ → ℂ) =ᵐ[volume]
      damp (𝓕 ((hF.2.choose_spec.2 b hb).1.toLp (slice F b)) : BoundaryL2) (a - b) := by
  obtain ⟨l, r, hl, hr, hv, hlr⟩ := verticalFourier_exists_endpoints hF a b ha hb
  apply spectral_transport_of_edges hF a b ha hb l r hl hr hlr
  intro t
  simpa only [sub_self] using ((hv t).2.sub (hv t).1)

/-- The native Fourier transforms of horizontal slices form a uniformly bounded
exponential transport family, starting only from holomorphy and the H² bound. -/
lemma spectral_family {F : ℂ → ℂ} (hF : IsH2 F) :
    ∃ d : ℝ → BoundaryL2, ∃ C : ℝ≥0,
      (∀ y : ℝ, 0 < y → eLpNorm (d y) 2 volume ≤ C) ∧
      (∀ y : ℝ, 0 < y → (d y : ℝ → ℂ) =ᵐ[volume] damp (d 1) (y - 1)) ∧
      (∀ y : ℝ, 0 < y → ((𝓕⁻ (d y) : BoundaryL2) : ℝ → ℂ) =ᵐ[volume] slice F y) := by
  obtain ⟨d, C, hb, hs, hd⟩ := spectral_family_basic hF
  refine ⟨d, C, hb, ?_, hs⟩
  intro y hy
  rw [hd y hy, hd 1 (by norm_num)]
  exact spectral_transport hF y 1 hy (by norm_num)

/-- Every Hardy function has a causal L² Fourier--Laplace density. -/
theorem representation_converse {F : ℂ → ℂ} (hF : IsH2 F) :
    ∃ f : ℝ → ℂ, Represents F f := by
  obtain ⟨d, C, hb, ht, hs⟩ := spectral_family hF
  exact represents_of_transport hF d C hb ht hs

/-- The representation equivalence uses no prescribed boundary datum. -/
theorem representation : Representation := by
  intro F
  constructor
  · exact representation_converse
  · rintro ⟨f, hf⟩
    exact represents_isH2 hf

/-- Strong boundary convergence follows for every Hardy function. -/
theorem boundary_convergence : BoundaryConvergence := by
  intro F hF
  obtain ⟨f, hf⟩ := representation_converse hF
  exact boundary_of_representation F f hf


end ExpandedFA.PartIV.HardyHalfPlaneRepresentation
