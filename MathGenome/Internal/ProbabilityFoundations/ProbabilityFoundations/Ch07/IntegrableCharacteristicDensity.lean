import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.TransformObjects
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.IntegrableCharacteristicDensity
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Analysis.Fourier.Inversion

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ComplexConjugate CompactlySupported FourierTransform

namespace ProbabilityFoundations.Ch07

lemma norm_inverseCharacteristicKernel {d : ℕ} (t x : Euclidean d) :
    ‖Complex.exp (-Complex.I * (inner ℝ t x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- The assumed frequency integrability justifies every inverse integral. -/
theorem inverseCharacteristicKernel_integrable {d : ℕ} (μ : Measure (Euclidean d))
    (hμ : Integrable (charFun μ)) (x : Euclidean d) :
    Integrable (fun t => Complex.exp (-Complex.I * (inner ℝ t x : ℂ)) * charFun μ t) := by
  apply hμ.norm.mono' ((by fun_prop : Continuous
    (fun t : Euclidean d => Complex.exp (-Complex.I * (inner ℝ t x : ℂ)))).aestronglyMeasurable.mul hμ.1)
  filter_upwards [] with t
  simp only [Pi.mul_apply, norm_mul, norm_inverseCharacteristicKernel, one_mul, le_refl]

/-- Dominated convergence gives continuity on the whole Euclidean space. -/
theorem inverseCharacteristicIntegral_continuous {d : ℕ} (μ : Measure (Euclidean d))
    (hμ : Integrable (charFun μ)) : Continuous (inverseCharacteristicIntegral μ) := by
  apply continuous_const.mul
  apply continuous_of_dominated
  · intro x
    exact (inverseCharacteristicKernel_integrable μ hμ x).1
  · intro x
    exact ae_of_all _ fun t => by rw [norm_mul, norm_inverseCharacteristicKernel, one_mul]
  · exact hμ.norm
  · filter_upwards [] with t
    fun_prop

/-- An explicit bound, independent of the spatial point. -/
theorem inverseCharacteristicIntegral_norm_le {d : ℕ} (μ : Measure (Euclidean d))
    (x : Euclidean d) :
    ‖inverseCharacteristicIntegral μ x‖ ≤
      (2 * Real.pi) ^ (-(d : ℝ)) * ∫ t : Euclidean d, ‖charFun μ t‖ := by
  unfold inverseCharacteristicIntegral
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  gcongr
  apply (norm_integral_le_integral_norm _).trans_eq
  congr 1
  ext t
  rw [norm_mul, norm_inverseCharacteristicKernel, one_mul]

/-- Hermitian symmetry makes the inverse integral real, even without the
frequency integrability assumption (Bochner integrals are totalized). -/
theorem inverseCharacteristicIntegral_im {d : ℕ} (μ : Measure (Euclidean d))
    (x : Euclidean d) : (inverseCharacteristicIntegral μ x).im = 0 := by
  have hconj : conj (inverseCharacteristicIntegral μ x) = inverseCharacteristicIntegral μ x := by
    unfold inverseCharacteristicIntegral
    rw [map_mul, Complex.conj_ofReal, ← integral_conj]
    congr 1
    rw [← integral_neg_eq_self]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [map_mul, ← Complex.exp_conj, map_neg, Complex.conj_I,
      Complex.conj_ofReal, neg_neg, inner_neg_left, Complex.ofReal_neg, charFun_neg,
      starRingEnd_self_apply]
    simp only [mul_neg, neg_mul]
  have h := congrArg Complex.im hconj
  simp only [Complex.conj_im] at h
  linarith

/-- Recover a Borel law from its integrals against compact continuous tests.
Local finiteness of the candidate measure follows from continuity, before
normalization or global integrability has been proved. -/
theorem measure_eq_withDensity_of_compact_integrals {d : ℕ}
    (μ : Measure (Euclidean d)) [IsFiniteMeasure μ] (f : Euclidean d → ℝ)
    (hc : Continuous f) (hn : ∀ x, 0 ≤ f x)
    (ht : ∀ u : C_c(Euclidean d, ℝ), ∫ x, u x ∂μ = ∫ x, u x * f x) :
    μ = volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  let ν : Measure (Euclidean d) := volume.withDensity (fun x => ENNReal.ofReal (f x))
  have : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hc
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro u
  rw [ht u, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (ae_of_all _ (by intro x; exact ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hn _), smul_eq_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => mul_comm _ _

/-- Once equality with a probability law is known, spatial integrability and
normalization follow; neither is an assumption of the recovery argument. -/
theorem density_integrable_and_normalized {d : ℕ}
    (μ : Measure (Euclidean d)) [IsProbabilityMeasure μ] (f : Euclidean d → ℝ)
    (hc : Continuous f) (hn : ∀ x, 0 ≤ f x)
    (heq : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    Integrable f ∧ (∫ x, f x) = 1 ∧
      ∀ A : Set (Euclidean d), MeasurableSet A →
        μ A = ENNReal.ofReal (∫ x in A, f x) := by
  have hm : Measurable (fun x => ENNReal.ofReal (f x)) := by fun_prop
  have ht : ∀ᵐ x ∂(volume : Measure (Euclidean d)), ENNReal.ofReal (f x) < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hi : Integrable (fun _ : Euclidean d => (1 : ℝ)) μ := integrable_const 1
  rw [heq] at hi
  have hf : Integrable f := by
    simpa only [ENNReal.toReal_ofReal (hn _), smul_eq_mul, mul_one] using
      (integrable_withDensity_iff_integrable_smul' hm ht).mp hi
  refine ⟨hf, ?_, ?_⟩
  · have h1 : (∫ _x : Euclidean d, (1 : ℝ) ∂μ) = 1 := by simp
    rw [heq, integral_withDensity_eq_integral_toReal_smul hm ht] at h1
    simpa only [ENNReal.toReal_ofReal (hn _), smul_eq_mul, mul_one] using h1
  · intro A hA
    rw [heq, withDensity_apply _ hA,
      ofReal_integral_eq_lintegral_ofReal hf.integrableOn (ae_of_all _ hn)]

private noncomputable def measureFourier {d : ℕ} (μ : Measure (Euclidean d)) (w : Euclidean d) : ℂ :=
  charFun μ ((-(2 * Real.pi) : ℝ) • w)

private lemma measureFourier_eq {d : ℕ} (μ : Measure (Euclidean d)) :
    measureFourier μ = VectorFourier.fourierIntegral Real.fourierChar μ
      (innerₗ (Euclidean d)) (fun _ => (1 : ℂ)) := by
  ext w
  simp only [measureFourier, charFun, VectorFourier.fourierIntegral,
    inner_smul_right, innerₗ_apply_apply, Circle.smul_def, Real.fourierChar_apply,
    smul_eq_mul, mul_one]
  congr 1
  ext y
  congr 1
  push_cast
  ring

private lemma measureFourier_integrable {d : ℕ} (μ : Measure (Euclidean d))
    (hμ : Integrable (charFun μ)) : Integrable (measureFourier μ) := by
  exact hμ.comp_smul (neg_ne_zero.mpr (by positivity) : (-(2 * Real.pi) : ℝ) ≠ 0)

private lemma inverse_eq_standard {d : ℕ} (μ : Measure (Euclidean d)) (x : Euclidean d) :
    inverseCharacteristicIntegral μ x =
      ∫ w : Euclidean d, Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x w : ℂ)) *
        measureFourier μ w := by
  have hc : |((-(2 * Real.pi)) ^ d)⁻¹| = (2 * Real.pi) ^ (-(d : ℝ)) := by
    rw [abs_inv, abs_pow, abs_neg, abs_of_pos (by positivity), Real.rpow_neg (by positivity),
      Real.rpow_natCast]
  have h := Measure.integral_comp_smul (volume : Measure (Euclidean d))
    (fun t => Complex.exp (-Complex.I * (inner ℝ t x : ℂ)) * charFun μ t)
    (-(2 * Real.pi))
  simp only [finrank_euclideanSpace, Fintype.card_fin, hc, RCLike.real_smul_eq_coe_mul] at h
  unfold inverseCharacteristicIntegral
  refine h.symm.trans ?_
  apply integral_congr_ae
  filter_upwards [] with w
  dsimp only [measureFourier]
  congr 2
  rw [inner_smul_left, real_inner_comm w x]
  simp only [starRingEnd_apply, star_trivial]
  push_cast
  ring

/-- A normalized Gaussian approximate identity. Its parameter tends to infinity. -/
private noncomputable def gaussianPeak {d : ℕ} (c : ℝ) (z : Euclidean d) : ℝ :=
  (Real.pi * c) ^ ((d : ℝ) / 2) * Real.exp (-Real.pi ^ 2 * c * ‖z‖ ^ 2)

private lemma gaussianPeak_nonneg {d : ℕ} {c : ℝ} (hc : 0 < c) (z : Euclidean d) :
    0 ≤ gaussianPeak c z := by unfold gaussianPeak; positivity

private lemma gaussianPeak_complex {d : ℕ} {c : ℝ} (hc : 0 < c) (z : Euclidean d) :
    (gaussianPeak c z : ℂ) =
      ((Real.pi * c : ℂ) ^ ((d : ℂ) / 2)) *
        Complex.exp (-Real.pi ^ 2 * c * (‖z‖ : ℂ) ^ 2) := by
  unfold gaussianPeak
  rw [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_cpow (by positivity)]
  push_cast
  rfl

private lemma gaussianPeak_integrable {d : ℕ} {c : ℝ} (hc : 0 < c) :
    Integrable (gaussianPeak (d := d) c) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Euclidean d) (b := ((Real.pi ^ 2 * c : ℝ) : ℂ))
    (show 0 < ((Real.pi ^ 2 * c : ℝ) : ℂ).re by exact_mod_cast (show 0 < Real.pi ^ 2 * c by positivity)) 0 0).norm
  simp only [zero_mul, add_zero, Complex.norm_exp] at h
  convert h.const_mul ((Real.pi * c) ^ ((d : ℝ) / 2)) using 1
  ext z
  simp [gaussianPeak, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_neg]

private lemma integral_gaussianPeak {d : ℕ} {c : ℝ} (hc : 0 < c) :
    ∫ z : Euclidean d, gaussianPeak c z = 1 := by
  unfold gaussianPeak
  rw [integral_const_mul]
  have he (z : Euclidean d) : -Real.pi ^ 2 * c * ‖z‖ ^ 2 = -(Real.pi ^ 2 * c) * ‖z‖ ^ 2 := by ring
  simp_rw [he]
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  have hh : Real.pi * c * (Real.pi / (Real.pi ^ 2 * c)) = 1 := by
    field_simp
  rw [hh, Real.one_rpow]

private lemma gaussianPeak_fourier_identity {d : ℕ} (μ : Measure (Euclidean d))
    [IsFiniteMeasure μ] {c : ℝ} (hc : 0 < c) (x : Euclidean d) :
    (∫ y, (gaussianPeak c (x - y) : ℂ) ∂μ) =
      ∫ w : Euclidean d,
        Complex.exp (-(c⁻¹ : ℝ) * (‖w‖ : ℂ) ^ 2 +
          2 * Real.pi * Complex.I * (inner ℝ x w : ℂ)) * measureFourier μ w := by
  have hg : Integrable (fun w : Euclidean d =>
      Complex.exp (-(c⁻¹ : ℝ) * (‖w‖ : ℂ) ^ 2 +
        2 * Real.pi * Complex.I * (inner ℝ x w : ℂ))) :=
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa using inv_pos.mpr hc) _ _
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ (Euclidean d)) Real.continuous_fourierChar continuous_inner
    (μ := μ) (ν := volume) (integrable_const (1 : ℂ)) hg
  simp only [flip_innerₗ, smul_eq_mul, one_mul] at h
  rw [← measureFourier_eq μ] at h
  calc
    _ = ∫ y, 𝓕 (fun w : Euclidean d =>
        Complex.exp (-(c⁻¹ : ℝ) * (‖w‖ : ℂ) ^ 2 +
          2 * Real.pi * Complex.I * (inner ℝ x w : ℂ))) y ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [fourier_gaussian_innerProductSpace' (by simpa using inv_pos.mpr hc)]
      rw [gaussianPeak_complex hc]
      congr 1
      · simp only [Complex.ofReal_inv, div_inv_eq_mul]
        simp
      · congr 1
        simp only [Complex.ofReal_inv, div_inv_eq_mul]
        ring
    _ = _ := by
      refine h.symm.trans ?_
      apply integral_congr_ae
      exact ae_of_all _ fun w => mul_comm _ _

private lemma gaussianPeak_limit {d : ℕ} (μ : Measure (Euclidean d))
    [IsFiniteMeasure μ] (hμ : Integrable (charFun μ)) (x : Euclidean d) :
    Tendsto (fun c : ℝ => ∫ y, (gaussianPeak c (x - y) : ℂ) ∂μ)
      atTop (𝓝 (inverseCharacteristicIntegral μ x)) := by
  have hmod : Integrable (fun w : Euclidean d =>
      Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x w : ℂ)) * measureFourier μ w) := by
    apply (measureFourier_integrable μ hμ).norm.mono'
      (((by fun_prop : Continuous (fun w : Euclidean d =>
        Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x w : ℂ))))).aestronglyMeasurable.mul
          (measureFourier_integrable μ hμ).1)
    filter_upwards [] with w
    simp only [Pi.mul_apply, norm_mul, Complex.norm_exp]
    simp
  have h := Real.tendsto_integral_cexp_sq_smul hmod
  rw [inverse_eq_standard μ x]
  apply h.congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
  rw [gaussianPeak_fourier_identity μ hc x]
  apply integral_congr_ae
  filter_upwards [] with w
  rw [smul_eq_mul, ← mul_assoc, ← Complex.exp_add]

/-- Nonnegativity comes from a limit of nonnegative Gaussian convolutions,
not from an assumed density of the original measure. -/
theorem inverseCharacteristicDensity_nonnegative {d : ℕ} (μ : Measure (Euclidean d))
    [IsFiniteMeasure μ] (hμ : Integrable (charFun μ)) (x : Euclidean d) :
    0 ≤ inverseCharacteristicDensity μ x := by
  have h := (Complex.continuous_re.tendsto _).comp (gaussianPeak_limit μ hμ x)
  change 0 ≤ (inverseCharacteristicIntegral μ x).re
  apply ge_of_tendsto h
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
  change 0 ≤ (∫ y, (gaussianPeak c (x - y) : ℂ) ∂μ).re
  rw [integral_complex_ofReal]
  simp only [Complex.ofReal_re]
  exact integral_nonneg fun y => gaussianPeak_nonneg hc _

private lemma gaussianPeak_test_integrable {d : ℕ} {c : ℝ} (hc : 0 < c)
    (u : C_c(Euclidean d, ℝ)) (y : Euclidean d) :
    Integrable (fun x => gaussianPeak c (y - x) * u x) := by
  apply ((gaussianPeak_integrable hc).comp_sub_left y).mul_bdd
      u.continuous.aestronglyMeasurable
      (ae_of_all _ fun x => u.toBoundedContinuousFunction.norm_coe_le_norm x)

private lemma gaussianPeak_test_norm_bound {d : ℕ} {c : ℝ} (hc : 0 < c)
    (u : C_c(Euclidean d, ℝ)) (y : Euclidean d) :
    (∫ x, ‖gaussianPeak c (y - x) * u x‖) ≤ ‖u.toBoundedContinuousFunction‖ := by
  calc
    _ ≤ ∫ x, gaussianPeak c (y - x) * ‖u.toBoundedContinuousFunction‖ := by
      apply integral_mono (gaussianPeak_test_integrable hc u y).norm
        (((gaussianPeak_integrable hc).comp_sub_left y).mul_const _)
      intro x
      change ‖gaussianPeak c (y - x) * u x‖ ≤ gaussianPeak c (y - x) * _
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (gaussianPeak_nonneg hc _)]
      exact mul_le_mul_of_nonneg_left (u.toBoundedContinuousFunction.norm_coe_le_norm x)
        (gaussianPeak_nonneg hc _)
    _ = _ := by
      rw [integral_mul_const, integral_sub_left_eq_self, integral_gaussianPeak hc, one_mul]

private lemma gaussianPeak_test_limit {d : ℕ} (u : C_c(Euclidean d, ℝ))
    (y : Euclidean d) :
    Tendsto (fun c : ℝ => ∫ x, gaussianPeak c (y - x) * u x) atTop (𝓝 (u y)) := by
  have h := Real.tendsto_integral_gaussian_smul'
    (u.integrable.ofReal : Integrable (fun x : Euclidean d => (u x : ℂ)))
    (v := y) (by fun_prop)
  have h' : Tendsto
      (fun c : ℝ => ∫ x, (gaussianPeak c (y - x) : ℂ) * (u x : ℂ))
      atTop (𝓝 (u y : ℂ)) := by
    apply h.congr'
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
    apply integral_congr_ae
    filter_upwards [] with x
    rw [gaussianPeak_complex hc]
    simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
    rfl
  have hh := (Complex.continuous_re.tendsto _).comp h'
  simpa only [Function.comp_def, ← Complex.ofReal_mul, integral_complex_ofReal,
    Complex.ofReal_re] using hh

private lemma gaussianPeak_even {d : ℕ} (c : ℝ) (x y : Euclidean d) :
    gaussianPeak c (x - y) = gaussianPeak c (y - x) := by
  simp only [gaussianPeak, norm_sub_rev x y]

private lemma gaussianPeak_test_prod_integrable {d : ℕ} (μ : Measure (Euclidean d))
    [IsFiniteMeasure μ] {c : ℝ} (hc : 0 < c) (u : C_c(Euclidean d, ℝ)) :
    Integrable (fun p : Euclidean d × Euclidean d =>
      gaussianPeak c (p.1 - p.2) * u p.2) (μ.prod volume) := by
  have hm : StronglyMeasurable (fun p : Euclidean d × Euclidean d =>
      gaussianPeak c (p.1 - p.2) * u p.2) := by
    apply Continuous.stronglyMeasurable
    unfold gaussianPeak
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ fun y => gaussianPeak_test_integrable hc u y, ?_⟩
  apply (integrable_const ‖u.toBoundedContinuousFunction‖).mono'
    hm.norm.integral_prod_right'.aestronglyMeasurable
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  exact gaussianPeak_test_norm_bound hc u y

private lemma gaussianPeak_test_average_limit {d : ℕ} (μ : Measure (Euclidean d))
    [IsFiniteMeasure μ] (u : C_c(Euclidean d, ℝ)) :
    Tendsto (fun c : ℝ => ∫ y, ∫ x, gaussianPeak c (y - x) * u x ∂volume ∂μ)
      atTop (𝓝 (∫ y, u y ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun _ => ‖u.toBoundedContinuousFunction‖)
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
    exact (gaussianPeak_test_prod_integrable μ hc u).integral_prod_left.1
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
    filter_upwards [] with y
    exact (norm_integral_le_integral_norm _).trans (gaussianPeak_test_norm_bound hc u y)
  · exact integrable_const _
  · exact ae_of_all _ fun y => gaussianPeak_test_limit u y

private lemma gaussianPeak_average_norm_bound {d : ℕ} (μ : Measure (Euclidean d))
    [IsFiniteMeasure μ] (hμ : Integrable (charFun μ)) {c : ℝ} (hc : 0 < c)
    (x : Euclidean d) :
    ‖∫ y, gaussianPeak c (x - y) ∂μ‖ ≤ ∫ w : Euclidean d, ‖measureFourier μ w‖ := by
  calc
    _ = ‖∫ y, (gaussianPeak c (x - y) : ℂ) ∂μ‖ := by
      rw [integral_complex_ofReal, Complex.norm_real]
    _ = ‖∫ w : Euclidean d,
        Complex.exp (-(c⁻¹ : ℝ) * (‖w‖ : ℂ) ^ 2 +
          2 * Real.pi * Complex.I * (inner ℝ x w : ℂ)) * measureFourier μ w‖ := by
      rw [gaussianPeak_fourier_identity μ hc x]
    _ ≤ _ := by
      apply norm_integral_le_of_norm_le (measureFourier_integrable μ hμ).norm
      filter_upwards [] with w
      rw [Complex.exp_add, norm_mul, norm_mul]
      have hp : ‖Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x w : ℂ))‖ = 1 := by
        simp [Complex.norm_exp]
      rw [hp, mul_one]
      apply mul_le_of_le_one_left (norm_nonneg _)
      rw [Complex.norm_exp, Real.exp_le_one_iff]
      have hr : (-(c⁻¹ : ℝ) * (‖w‖ : ℂ) ^ 2).re = -(c⁻¹) * ‖w‖ ^ 2 := by
        norm_cast
      rw [hr]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (inv_nonneg.mpr hc.le)) (sq_nonneg _)

private lemma gaussianPeak_average_test_limit {d : ℕ} (μ : Measure (Euclidean d))
    [IsFiniteMeasure μ] (hμ : Integrable (charFun μ)) (u : C_c(Euclidean d, ℝ)) :
    Tendsto (fun c : ℝ => ∫ x, u x * (∫ y, gaussianPeak c (x - y) ∂μ)) atTop
      (𝓝 (∫ x, u x * inverseCharacteristicDensity μ x)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖u x‖ * ∫ w : Euclidean d, ‖measureFourier μ w‖)
  · filter_upwards [] with c
    have hm : StronglyMeasurable (fun p : Euclidean d × Euclidean d =>
        gaussianPeak c (p.1 - p.2)) := by
      apply Continuous.stronglyMeasurable
      unfold gaussianPeak
      fun_prop
    exact u.continuous.aestronglyMeasurable.mul hm.integral_prod_right'.aestronglyMeasurable
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
    filter_upwards [] with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (gaussianPeak_average_norm_bound μ hμ hc x) (norm_nonneg _)
  · exact u.integrable.norm.mul_const _
  · filter_upwards [] with x
    apply Tendsto.const_mul
    have h := (Complex.continuous_re.tendsto _).comp (gaussianPeak_limit μ hμ x)
    simpa only [Function.comp_def, integral_complex_ofReal, Complex.ofReal_re,
      inverseCharacteristicDensity] using h

/-- Compact continuous tests identify the inverse integral with the original law. -/
theorem inverseCharacteristicDensity_compact_integrals {d : ℕ}
    (μ : Measure (Euclidean d)) [IsFiniteMeasure μ] (hμ : Integrable (charFun μ))
    (u : C_c(Euclidean d, ℝ)) :
    (∫ x, u x ∂μ) = ∫ x, u x * inverseCharacteristicDensity μ x := by
  apply tendsto_nhds_unique (gaussianPeak_test_average_limit μ u)
  apply (gaussianPeak_average_test_limit μ hμ u).congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
  symm
  calc
    _ = ∫ x, ∫ y, gaussianPeak c (y - x) * u x ∂μ :=
      integral_integral_swap (gaussianPeak_test_prod_integrable μ hc u)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        change gaussianPeak c (y - x) * u x = u x * gaussianPeak c (x - y)
        rw [gaussianPeak_even c y x, mul_comm]

/-- An integrable characteristic function has the everywhere defined bounded
continuous nonnegative inverse density, and this density recovers every Borel
set of the original probability law. -/
theorem integrable_characteristicFunction_density :
    Specs.ProbabilityFoundations.Ch07.IntegrableCharacteristicDensity.DensityTheorem := by
  intro d μ inst hμ
  have hc : Continuous (inverseCharacteristicDensity μ) :=
    Complex.continuous_re.comp (inverseCharacteristicIntegral_continuous μ hμ)
  have hn : ∀ x, 0 ≤ inverseCharacteristicDensity μ x :=
    inverseCharacteristicDensity_nonnegative μ hμ
  have heq : μ = volume.withDensity (fun x =>
      ENNReal.ofReal (inverseCharacteristicDensity μ x)) :=
    measure_eq_withDensity_of_compact_integrals μ _ hc hn
      (inverseCharacteristicDensity_compact_integrals μ hμ)
  obtain ⟨hi, h1, hA⟩ := density_integrable_and_normalized μ _ hc hn heq
  refine ⟨inverseCharacteristicIntegral_im μ, hn, hc, ?_, hi, h1, heq, hA⟩
  refine ⟨(2 * Real.pi) ^ (-(d : ℝ)) * ∫ t : Euclidean d, ‖charFun μ t‖, ?_⟩
  intro x
  exact (Complex.abs_re_le_norm _).trans (inverseCharacteristicIntegral_norm_le μ x)

end ProbabilityFoundations.Ch07
