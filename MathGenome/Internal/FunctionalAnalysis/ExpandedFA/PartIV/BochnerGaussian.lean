import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.BochnerGaussian
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.PositiveDefiniteContinuity
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped FourierTransform

namespace ExpandedFA.PartIV.BochnerGaussian
open ExpandedFA.Fourier
open PositiveDefiniteContinuity

lemma gaussianFactor_pos {d : ℕ} (ε : ℝ) (x : Euclidean d) :
    0 < gaussianFactor ε x := Real.exp_pos _

@[simp] lemma gaussianFactor_zero {d : ℕ} (ε : ℝ) :
    gaussianFactor (d := d) ε 0 = 1 := by simp [gaussianFactor]

@[simp] lemma damped_zero {d : ℕ} (φ : Euclidean d → ℂ) (ε : ℝ) :
    damped φ ε 0 = φ 0 := by simp [damped]

@[fun_prop] lemma continuous_gaussianFactor {d : ℕ} (ε : ℝ) :
    Continuous (gaussianFactor (d := d) ε) := by unfold gaussianFactor; fun_prop

/-- A bound with the exact original mass; it also handles mass zero. -/
lemma norm_damped_le {d : ℕ} {φ : Euclidean d → ℂ}
    (hφ : PositiveDefiniteContinuity.Spec.PositiveDefinite φ) (ε : ℝ) (x : Euclidean d) :
    ‖damped φ ε x‖ ≤ (φ 0).re * gaussianFactor ε x := by
  rw [damped, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (gaussianFactor_pos ε x)]
  exact mul_le_mul_of_nonneg_right (norm_le_value_zero hφ x) (gaussianFactor_pos ε x).le

theorem damping_continuous : Spec.DampingContinuous := by
  intro d φ hφ hcont ε
  exact (uniformContinuous_of_continuousAt_zero hφ hcont).continuous.mul
    (Complex.continuous_ofReal.comp (continuous_gaussianFactor ε))

lemma integrable_gaussianFactor {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    Integrable (gaussianFactor (d := d) ε) := by
  have hb : 0 < ((Real.pi * ε : ℝ) : ℂ).re := by
    simpa using mul_pos Real.pi_pos hε
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Euclidean d) hb 0 0
  have hr := h.re
  change Integrable (fun x : Euclidean d => Real.exp (-Real.pi * ε * ‖x‖ ^ 2))
  simpa [gaussianFactor, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_neg, ← Complex.ofReal_exp, neg_mul, mul_assoc] using hr

theorem damping_integrable : Spec.DampingIntegrable := by
  intro d φ hφ hcont ε hε
  exact ((integrable_gaussianFactor hε).const_mul (φ 0).re).mono'
    (damping_continuous d φ hφ hcont ε).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_damped_le hφ ε))

/-- Agreement with the native integral Fourier transform, for use with its
inversion and dominated-convergence API. No integrability is needed here. -/
lemma integralFourier_eq_native {d : ℕ} (f : Euclidean d → ℂ) :
    integralFourier f = 𝓕 f := by
  ext ξ
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul]
  congr 2
  rw [real_inner_comm ξ x]
  push_cast
  ring

lemma inversion_of_density_integrable {d : ℕ} {φ : Euclidean d → ℂ}
    (hφ : PositiveDefiniteContinuity.Spec.PositiveDefinite φ) (hcont : ContinuousAt φ 0)
    {ε : ℝ} (hε : 0 < ε) (hF : Integrable (density φ ε)) (x : Euclidean d) :
    damped φ ε x = ∫ ξ : Euclidean d,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x ξ : ℝ)) *
        density φ ε ξ := by
  have hFn : Integrable (𝓕 (damped φ ε)) := by
    rwa [← integralFourier_eq_native, ← density]
  have hinv := (damping_integrable d φ hφ hcont ε hε).fourierInv_fourier_eq hFn
    ((damping_continuous d φ hφ hcont ε).continuousAt (x := x))
  rw [Real.fourierInv_eq'] at hinv
  rw [← hinv]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [density, integralFourier_eq_native]
  simp only [smul_eq_mul]
  congr 2
  rw [real_inner_comm ξ x]
  push_cast
  ring

lemma integral_density_of_integrable {d : ℕ} {φ : Euclidean d → ℂ}
    (hφ : PositiveDefiniteContinuity.Spec.PositiveDefinite φ) (hcont : ContinuousAt φ 0)
    {ε : ℝ} (hε : 0 < ε) (hF : Integrable (density φ ε)) :
    ∫ ξ, density φ ε ξ = φ 0 := by
  simpa using (inversion_of_density_integrable hφ hcont hε hF 0).symm

lemma density_eq_ofReal {d : ℕ} {φ : Euclidean d → ℂ} {ε : ℝ}
    (hreal : ∀ ξ, (density φ ε ξ).im = 0) (ξ : Euclidean d) :
    ((density φ ε ξ).re : ℂ) = density φ ε ξ := by
  apply Complex.ext <;> simp [hreal]

lemma densityMeasure_finite {d : ℕ} {φ : Euclidean d → ℂ} {ε : ℝ}
    (hF : Integrable (density φ ε)) (hpos : ∀ ξ, 0 ≤ (density φ ε ξ).re) :
    IsFiniteMeasure (densityMeasure φ ε) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal
    (f := fun ξ => (density φ ε ξ).re) hF.re (Filter.Eventually.of_forall hpos)]
  exact ENNReal.ofReal_ne_top

lemma densityMeasure_regular {d : ℕ} {φ : Euclidean d → ℂ} {ε : ℝ}
    (hF : Integrable (density φ ε)) (hpos : ∀ ξ, 0 ≤ (density φ ε ξ).re) :
    Measure.Regular (densityMeasure φ ε) := by
  have := densityMeasure_finite hF hpos
  infer_instance

lemma densityMeasure_mass {d : ℕ} {φ : Euclidean d → ℂ}
    (hφ : PositiveDefiniteContinuity.Spec.PositiveDefinite φ) (hcont : ContinuousAt φ 0)
    {ε : ℝ} (hε : 0 < ε) (hF : Integrable (density φ ε))
    (hpos : ∀ ξ, 0 ≤ (density φ ε ξ).re) :
    densityMeasure φ ε Set.univ = ENNReal.ofReal (φ 0).re := by
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
    (f := fun ξ => (density φ ε ξ).re) hF.re (Filter.Eventually.of_forall hpos)]
  congr 1
  calc
    (∫ ξ, (density φ ε ξ).re) = (∫ ξ, density φ ε ξ).re := integral_re hF
    _ = (φ 0).re := congrArg Complex.re (integral_density_of_integrable hφ hcont hε hF)

lemma representation_of_fourier_properties {d : ℕ} {φ : Euclidean d → ℂ}
    (hφ : PositiveDefiniteContinuity.Spec.PositiveDefinite φ) (hcont : ContinuousAt φ 0)
    {ε : ℝ} (hε : 0 < ε) (hF : Integrable (density φ ε))
    (hreal : ∀ ξ, (density φ ε ξ).im = 0)
    (hpos : ∀ ξ, 0 ≤ (density φ ε ξ).re) (x : Euclidean d) :
    damped φ ε x = ∫ ξ,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x ξ : ℝ))
      ∂densityMeasure φ ε := by
  have hmeas : AEMeasurable (fun ξ => ENNReal.ofReal (density φ ε ξ).re) volume :=
    hF.re.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [densityMeasure, integral_withDensity_eq_integral_toReal_smul₀ hmeas
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  rw [inversion_of_density_integrable hφ hcont hε hF x]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [ENNReal.toReal_ofReal (hpos ξ), Algebra.smul_def]
  change _ = ((density φ ε ξ).re : ℂ) * _
  rw [density_eq_ofReal hreal ξ]
  exact mul_comm _ _

/-- Gaussian inversion with its positive, real normalizing factor. -/
lemma gaussian_character_integral {d : ℕ} {ε : ℝ} (hε : 0 < ε) (x : Euclidean d) :
    (∫ ξ : Euclidean d, (gaussianFactor ε⁻¹ ξ : ℂ) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x ξ : ℝ))) =
    ((ε ^ (Module.finrank ℝ (Euclidean d) / 2 : ℝ) : ℝ) : ℂ) *
      (gaussianFactor ε x : ℂ) := by
  have hb : 0 < ((Real.pi : ℂ) * (ε : ℂ)⁻¹).re := by
    simp only [← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
    positivity
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have he : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
  calc
    _ = ∫ ξ : Euclidean d, Complex.exp
        (-((Real.pi : ℂ) * (ε : ℂ)⁻¹) * ‖ξ‖ ^ 2 +
          (2 * (Real.pi : ℂ) * Complex.I) * (inner ℝ x ξ : ℝ)) := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [gaussianFactor, Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = _ := GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb _ x
    _ = _ := by
      congr 1
      · rw [Complex.ofReal_cpow hε.le]
        push_cast
        congr 1
        field_simp
      · rw [gaussianFactor, Complex.ofReal_exp]
        congr 1
        push_cast
        simp only [mul_pow, Complex.I_sq]
        field_simp
        ring

/-- Positive definiteness is preserved under pointwise integrable positive
mixtures. The proof uses only finite sums, not a representation theorem. -/
lemma positiveDefinite_integral {Ω G : Type*} [MeasurableSpace Ω] [AddGroup G]
    (μ : Measure Ω) (F : Ω → G → ℂ)
    (hint : ∀ x, Integrable (fun ω => F ω x) μ)
    (hpos : ∀ ω, PositiveDefiniteContinuity.Spec.PositiveDefinite (F ω)) :
    PositiveDefiniteContinuity.Spec.PositiveDefinite (fun x => ∫ ω, F ω x ∂μ) := by
  intro n x a
  let Q : Ω → ℂ := fun ω => ∑ j, ∑ k,
    starRingEnd ℂ (a j) * a k * F ω (x k - x j)
  have ht (j k : Fin n) : Integrable
      (fun ω => starRingEnd ℂ (a j) * a k * F ω (x k - x j)) μ :=
    (hint _).const_mul _
  have hs (j : Fin n) : Integrable
      (fun ω => ∑ k, starRingEnd ℂ (a j) * a k * F ω (x k - x j)) μ :=
    integrable_finsetSum _ (fun k _ => ht j k)
  have hQ : Integrable Q μ := integrable_finsetSum _ (fun j _ => hs j)
  have heq : (∑ j, ∑ k, starRingEnd ℂ (a j) * a k * ∫ ω, F ω (x k - x j) ∂μ) =
      ∫ ω, Q ω ∂μ := by
    symm
    rw [show Q = (fun ω => ∑ j, ∑ k,
      starRingEnd ℂ (a j) * a k * F ω (x k - x j)) from rfl,
      integral_finsetSum _ (fun j _ => hs j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finsetSum _ (fun k _ => ht j k)]
    simp_rw [integral_const_mul]
  rw [heq]
  constructor
  · calc
      (∫ ω, Q ω ∂μ).im = ∫ ω, (Q ω).im ∂μ := (integral_im hQ).symm
      _ = 0 := by simp only [Q, fun ω => (hpos ω n x a).1, integral_zero]
  · calc
      0 ≤ ∫ ω, (Q ω).re ∂μ := integral_nonneg (fun ω => (hpos ω n x a).2)
      _ = (∫ ω, Q ω ∂μ).re := integral_re hQ

lemma positiveDefinite_nonneg_mul {G : Type*} [AddGroup G] {φ : G → ℂ}
    (hφ : PositiveDefiniteContinuity.Spec.PositiveDefinite φ) {c : ℝ} (hc : 0 ≤ c) :
    PositiveDefiniteContinuity.Spec.PositiveDefinite (fun x => (c : ℂ) * φ x) := by
  intro n x a
  have heq : (∑ j, ∑ k, starRingEnd ℂ (a j) * a k * ((c : ℂ) * φ (x k - x j))) =
      (c : ℂ) * ∑ j, ∑ k, starRingEnd ℂ (a j) * a k * φ (x k - x j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [heq]
  simpa only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, add_zero, sub_zero, (hφ n x a).1] using
    And.intro (mul_zero c) (mul_nonneg hc (hφ n x a).2)

lemma positiveDefinite_character_mul {G : Type*} [AddGroup G] {φ χ : G → ℂ}
    (hφ : PositiveDefiniteContinuity.Spec.PositiveDefinite φ)
    (hχ : ∀ x y, starRingEnd ℂ (χ x) * χ y = χ (y - x)) :
    PositiveDefiniteContinuity.Spec.PositiveDefinite (fun x => φ x * χ x) := by
  intro n x a
  have heq : (∑ j, ∑ k,
      starRingEnd ℂ (a j) * a k * (φ (x k - x j) * χ (x k - x j))) =
      ∑ j, ∑ k, starRingEnd ℂ (a j * χ (x j)) * (a k * χ (x k)) * φ (x k - x j) := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [← hχ, map_mul]
    ring
  rw [heq]
  exact hφ n x (fun j => a j * χ (x j))

/-- A character in the manuscript's positive-sign normalization. -/
def character {d : ℕ} (x ξ : Euclidean d) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x ξ : ℝ))

lemma character_conj_mul {d : ℕ} (x y ξ : Euclidean d) :
    starRingEnd ℂ (character x ξ) * character y ξ = character (y - x) ξ := by
  simp only [character, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, inner_sub_left,
    Complex.ofReal_sub]
  ring

@[simp] lemma norm_character {d : ℕ} (x ξ : Euclidean d) : ‖character x ξ‖ = 1 := by
  simp [character, Complex.norm_exp]

lemma continuous_character {d : ℕ} (x : Euclidean d) : Continuous (character x) := by
  unfold character
  fun_prop

/-- No continuity assumption on φ is needed for preservation of positivity. -/
lemma positiveDefinite_damped {d : ℕ} {φ : Euclidean d → ℂ}
    (hφ : PositiveDefiniteContinuity.Spec.PositiveDefinite φ) {ε : ℝ} (hε : 0 < ε) :
    PositiveDefiniteContinuity.Spec.PositiveDefinite (damped φ ε) := by
  let C : ℝ := ε ^ (Module.finrank ℝ (Euclidean d) / 2 : ℝ)
  have hC : 0 < C := Real.rpow_pos_of_pos hε _
  let F : Euclidean d → Euclidean d → ℂ := fun ξ x =>
    (gaussianFactor ε⁻¹ ξ : ℂ) * (φ x * character x ξ)
  have hint (x : Euclidean d) : Integrable (fun ξ => F ξ x) := by
    have hg : Integrable (fun ξ : Euclidean d => (gaussianFactor ε⁻¹ ξ : ℂ)) :=
      (integrable_gaussianFactor (inv_pos.mpr hε)).ofReal
    have hi := hg.mul_bdd (continuous_character x).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => (norm_character x ξ).le))
    convert hi.const_mul (φ x) using 1
    funext ξ
    dsimp [F]
    ring
  have hpos (ξ : Euclidean d) : PositiveDefiniteContinuity.Spec.PositiveDefinite (F ξ) :=
    positiveDefinite_nonneg_mul
      (positiveDefinite_character_mul hφ (fun x y => character_conj_mul x y ξ))
      (gaussianFactor_pos ε⁻¹ ξ).le
  have hid (x : Euclidean d) : (∫ ξ, F ξ x) = (C : ℂ) * damped φ ε x := by
    calc
      _ = φ x * ∫ ξ : Euclidean d, (gaussianFactor ε⁻¹ ξ : ℂ) * character x ξ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with ξ
        dsimp [F]
        ring
      _ = _ := by
        rw [show (∫ ξ : Euclidean d, (gaussianFactor ε⁻¹ ξ : ℂ) * character x ξ) =
          (C : ℂ) * (gaussianFactor ε x : ℂ) from gaussian_character_integral hε x]
        dsimp [damped]
        ring
  have hp : PositiveDefiniteContinuity.Spec.PositiveDefinite
      (fun x => (C : ℂ) * damped φ ε x) := by
    convert positiveDefinite_integral volume F hint hpos using 1
    funext x
    exact (hid x).symm
  have hp' := positiveDefinite_nonneg_mul hp (inv_nonneg.mpr hC.le)
  simpa only [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hC.ne',
    Complex.ofReal_one, one_mul] using hp'

theorem damping_positive_definite : Spec.DampingPositiveDefinite := by
  intro d φ hφ _ ε hε
  exact positiveDefinite_damped hφ hε

lemma density_continuous {d : ℕ} {φ : Euclidean d → ℂ}
    (hφ : PositiveDefiniteContinuity.Spec.PositiveDefinite φ) (hcont : ContinuousAt φ 0)
    {ε : ℝ} (hε : 0 < ε) : Continuous (density φ ε) := by
  rw [density, integralFourier_eq_native]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ (damping_integrable d φ hφ hcont ε hε)

/-- Hermitian symmetry makes the integral Fourier transform real. -/
lemma fourier_im_eq_zero {d : ℕ} {f : Euclidean d → ℂ}
    (hf : PositiveDefiniteContinuity.Spec.PositiveDefinite f) (ξ : Euclidean d) :
    (integralFourier f ξ).im = 0 := by
  have hc : starRingEnd ℂ (integralFourier f ξ) = integralFourier f ξ := by
    rw [integralFourier, ← integral_conj]
    calc
      (∫ x : Euclidean d, starRingEnd ℂ
        (Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x ξ : ℝ)) * f x)) =
          ∫ x : Euclidean d,
            Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ (-x) ξ : ℝ)) * f (-x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [map_mul, ← Complex.exp_conj]
        have hh := conjugate_neg hf (-x)
        simp only [neg_neg] at hh
        rw [← hh]
        congr 2
        simp only [map_mul, map_neg, map_ofNat, Complex.conj_ofReal,
          Complex.conj_I, inner_neg_left, Complex.ofReal_neg]
        ring
      _ = _ := integral_neg_eq_self
        (fun x : Euclidean d =>
          Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x ξ : ℝ)) * f x) volume
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  linarith

/-- Abel summation of the Fourier transform at zero requires no integrability
of that Fourier transform. Fubini is justified by the integrable Gaussian. -/
lemma tendsto_gaussian_fourier_integral {d : ℕ} {f : Euclidean d → ℂ}
    (hf : Integrable f) (hc : ContinuousAt f 0) :
    Filter.Tendsto (fun c : ℝ => ∫ ξ : Euclidean d,
      Complex.exp (-(c⁻¹ : ℂ) * ‖ξ‖ ^ 2) * 𝓕 f ξ)
      Filter.atTop (nhds (f 0)) := by
  apply (Real.tendsto_integral_gaussian_smul' hf hc).congr'
  filter_upwards [Filter.Ioi_mem_atTop (0 : ℝ)] with c (hc : 0 < c)
  have hg : Integrable (fun ξ : Euclidean d =>
      Complex.exp (-(c⁻¹ : ℂ) * ‖ξ‖ ^ 2)) := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := Euclidean d) (b := (c⁻¹ : ℂ)) (by simpa using inv_pos.mpr hc) 0 0
  have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ (Euclidean d)) Real.continuous_fourierChar continuous_inner hf hg
  have hflip : (innerₗ (Euclidean d)).flip = innerₗ (Euclidean d) := by
    exact flip_innerₗ (Euclidean d)
  rw [hflip] at hswap
  change (∫ ξ, 𝓕 f ξ * Complex.exp (-(c⁻¹ : ℂ) * ‖ξ‖ ^ 2)) =
    (∫ x, f x * 𝓕 (fun ξ : Euclidean d =>
      Complex.exp (-(c⁻¹ : ℂ) * ‖ξ‖ ^ 2)) x) at hswap
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun ξ => mul_comm _ _)), hswap]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [fourier_gaussian_innerProductSpace (by simpa using inv_pos.mpr hc)]
  simp only [zero_sub, norm_neg, smul_eq_mul]
  rw [mul_comm (f x)]
  congr 1
  · congr 1 <;> simp [div_inv_eq_mul, mul_assoc, mul_comm]

/-- Positive inversion: a real nonnegative Fourier transform of an integrable
function continuous at zero is integrable. This does not assume inversion. -/
lemma integrable_fourier_of_nonnegative {d : ℕ} {f : Euclidean d → ℂ}
    (hf : Integrable f) (hc : ContinuousAt f 0)
    (hreal : ∀ ξ, (𝓕 f ξ).im = 0) (hpos : ∀ ξ, 0 ≤ (𝓕 f ξ).re) :
    Integrable (𝓕 f) := by
  let g : ℕ → Euclidean d → ℝ := fun n ξ =>
    Real.exp (-((n + 1 : ℝ)⁻¹) * ‖ξ‖ ^ 2) * (𝓕 f ξ).re
  have hfc : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf
  have hi (n : ℕ) : Integrable (fun ξ : Euclidean d =>
      Complex.exp (-(((n + 1 : ℝ)⁻¹) : ℂ) * ‖ξ‖ ^ 2) * 𝓕 f ξ) := by
    have hg : Integrable (fun ξ : Euclidean d =>
        Complex.exp (-(((n + 1 : ℝ)⁻¹) : ℂ) * ‖ξ‖ ^ 2)) := by
      simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
        (V := Euclidean d) (b := (((n + 1 : ℝ)⁻¹) : ℂ)) (by norm_cast; positivity) 0 0
    exact hg.mul_bdd hfc.aestronglyMeasurable
      (Filter.Eventually.of_forall (Real.norm_fourier_le_integral_norm f))
  have he (n : ℕ) (ξ : Euclidean d) : g n ξ =
      (Complex.exp (-(((n + 1 : ℝ)⁻¹) : ℂ) * ‖ξ‖ ^ 2) * 𝓕 f ξ).re := by
    simp only [g, ← Complex.ofReal_inv, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hgi (n : ℕ) : Integrable (g n) := by
    convert (hi n).re using 1
    funext ξ
    exact he n ξ
  have hgn (n : ℕ) (ξ : Euclidean d) : 0 ≤ g n ξ :=
    mul_nonneg (Real.exp_pos _).le (hpos ξ)
  have hgt (ξ : Euclidean d) : Filter.Tendsto (fun n => g n ξ)
      Filter.atTop (nhds ((𝓕 f ξ).re)) := by
    have hi : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℝ)⁻¹))
        Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp
        (Filter.tendsto_atTop_add_const_right Filter.atTop 1 tendsto_natCast_atTop_atTop)
    simpa [g] using ((Real.continuous_exp.continuousAt.tendsto.comp
      (hi.neg.mul_const (‖ξ‖ ^ 2))).mul_const (𝓕 f ξ).re)
  have hlim : Filter.Tendsto (fun n => ∫ ξ, g n ξ) Filter.atTop (nhds (f 0).re) := by
    have ht := (tendsto_gaussian_fourier_integral hf hc).comp
      (Filter.tendsto_atTop_add_const_right Filter.atTop 1 tendsto_natCast_atTop_atTop)
    have ht' := Complex.continuous_re.continuousAt.tendsto.comp ht
    convert ht' using 1
    funext n
    calc
      (∫ ξ, g n ξ) = ∫ ξ, (Complex.exp
        (-(((n + 1 : ℝ)⁻¹) : ℂ) * ‖ξ‖ ^ 2) * 𝓕 f ξ).re :=
          integral_congr_ae (Filter.Eventually.of_forall (he n))
      _ = _ := integral_re (hi n)
  have hle : (∫⁻ ξ, ENNReal.ofReal (𝓕 f ξ).re) ≤ ENNReal.ofReal (f 0).re := by
    have hfatou := lintegral_liminf_le' (u := Filter.atTop) (μ := (volume : Measure (Euclidean d)))
      (fun n => (hgi n).aemeasurable.ennreal_ofReal)
    have ht (ξ : Euclidean d) := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hgt ξ)
    simp_rw [show ∀ ξ, Filter.liminf (fun n => ENNReal.ofReal (g n ξ)) Filter.atTop =
      ENNReal.ofReal (𝓕 f ξ).re from fun ξ => (ht ξ).liminf_eq] at hfatou
    have heq (n : ℕ) : (∫⁻ ξ, ENNReal.ofReal (g n ξ)) =
        ENNReal.ofReal (∫ ξ, g n ξ) :=
      (ofReal_integral_eq_lintegral_ofReal (hgi n)
        (Filter.Eventually.of_forall (hgn n))).symm
    simp_rw [heq] at hfatou
    exact hfatou.trans_eq
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim).liminf_eq
  have hr : Integrable (fun ξ => (𝓕 f ξ).re) := by
    refine ⟨(Complex.continuous_re.comp hfc).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hpos)]
    exact hle.trans_lt ENNReal.ofReal_lt_top
  convert hr.ofReal using 1
  funext ξ
  apply Complex.ext <;> simp [hreal]

/-- Averaging finite positive quadratic sums over independent samples gives
positivity of the kernel integral. Diagonal terms disappear after division by
sample size; no measure representation theorem is used. -/
lemma positiveDefinite_probability_integral {d : ℕ} {f : Euclidean d → ℂ}
    (hf : PositiveDefiniteContinuity.Spec.PositiveDefinite f) (hc : Continuous f)
    (μ : Measure (Euclidean d)) [IsProbabilityMeasure μ] :
    0 ≤ ∫ p : Euclidean d × Euclidean d, (f (p.2 - p.1)).re ∂μ.prod μ := by
  classical
  let B : ℝ := ∫ p : Euclidean d × Euclidean d, (f (p.2 - p.1)).re ∂μ.prod μ
  let M : ℝ := (f 0).re
  have havg (n : ℕ) : 0 ≤ (n : ℝ) * ((n : ℝ) * B + M - B) := by
    let ν : Measure (Fin n → Euclidean d) := Measure.pi (fun _ => μ)
    have ht (j k : Fin n) : Integrable (fun ω : Fin n → Euclidean d =>
        (f (ω k - ω j)).re) ν := by
      apply (integrable_const M).mono'
        (Complex.continuous_re.comp (hc.comp (by fun_prop))).aestronglyMeasurable
      filter_upwards [] with ω
      exact (Complex.abs_re_le_norm _).trans (norm_le_value_zero hf _)
    have he (j k : Fin n) : (∫ ω : Fin n → Euclidean d,
        (f (ω k - ω j)).re ∂ν) = B + if k = j then M - B else 0 := by
      by_cases h : j = k
      · subst k
        simp [M]
      · have hind := (ProbabilityTheory.iIndepFun_pi
          (μ := fun _ : Fin n => μ) (X := fun _ => id)
          (fun _ => measurable_id.aemeasurable)).indepFun h
        have hm : Measure.map (fun ω : Fin n → Euclidean d => (ω j, ω k)) ν =
            μ.prod μ := by
          have he := hind.map_prod_eq_prod_map_map
            ((measurable_pi_apply j).aemeasurable)
            ((measurable_pi_apply k).aemeasurable)
          simpa only [id_eq, (measurePreserving_eval (fun _ : Fin n => μ) j).map_eq,
            (measurePreserving_eval (fun _ : Fin n => μ) k).map_eq, ν] using he
        have ha : AEStronglyMeasurable (fun p : Euclidean d × Euclidean d =>
            (f (p.2 - p.1)).re) (μ.prod μ) :=
          (Complex.continuous_re.comp (hc.comp (by fun_prop))).aestronglyMeasurable
        rw [ite_eq_right (Ne.symm h), add_zero]
        rw [← hm] at ha
        exact (integral_map (μ := ν)
          (φ := fun ω : Fin n → Euclidean d => (ω j, ω k))
          (f := fun p : Euclidean d × Euclidean d => (f (p.2 - p.1)).re)
          ((measurable_pi_apply j).prodMk (measurable_pi_apply k)).aemeasurable ha).symm.trans
          (by rw [hm])
    have hs (j : Fin n) := integrable_finsetSum Finset.univ (fun k _ => ht j k)
    have hQ : 0 ≤ ∫ ω : Fin n → Euclidean d,
        ∑ j : Fin n, ∑ k : Fin n, (f (ω k - ω j)).re ∂ν := by
      apply integral_nonneg
      intro ω
      have h := (hf n ω (fun _ => 1)).2
      simpa using h
    rw [integral_finsetSum _ (fun j _ => hs j)] at hQ
    simp_rw [integral_finsetSum _ (fun k _ => ht _ k), he] at hQ
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hQ
    convert hQ using 1; ring
  by_contra hn
  have hB : B < 0 := lt_of_not_ge hn
  obtain ⟨n, hn⟩ := exists_nat_gt ((M - B) / (-B))
  have hn' : (M - B) / (-B) < (n + 1 : ℝ) := by
    exact hn.trans (by linarith)
  have hi := (div_lt_iff₀ (neg_pos.mpr hB)).mp hn'
  have hq := havg (n + 1)
  push_cast at hq
  have hp : 0 < (n + 1 : ℝ) := by positivity
  have hq' := (mul_nonneg_iff_of_pos_left hp).mp hq
  nlinarith

/-- The same positivity holds for every finite positive measure, including
zero mass, by normalization. -/
lemma positiveDefinite_finite_integral {d : ℕ} {f : Euclidean d → ℂ}
    (hf : PositiveDefiniteContinuity.Spec.PositiveDefinite f) (hc : Continuous f)
    (μ : Measure (Euclidean d)) [IsFiniteMeasure μ] :
    0 ≤ ∫ p : Euclidean d × Euclidean d, (f (p.2 - p.1)).re ∂μ.prod μ := by
  by_cases hμ : μ = 0
  · simp [hμ]
  have hm : μ Set.univ ≠ 0 := by simpa using hμ
  let ν : Measure (Euclidean d) := (μ Set.univ)⁻¹ • μ
  have hp : IsProbabilityMeasure ν := by
    constructor
    simp only [ν, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hm (measure_ne_top _ _)
  have ht := positiveDefinite_probability_integral hf hc ν
  dsimp only [ν] at ht
  rw [Measure.prod_smul_left, Measure.prod_smul_right,
    integral_smul_measure, integral_smul_measure] at ht
  simp only [smul_eq_mul] at ht
  have hmass : 0 < ((μ Set.univ)⁻¹).toReal :=
    ENNReal.toReal_pos (by simp) (by simp [hm])
  exact (mul_nonneg_iff_of_pos_left hmass).mp
    ((mul_nonneg_iff_of_pos_left hmass).mp ht)

/-- Completing the square for the overlap of two real Gaussians. -/
lemma gaussianFactor_overlap {d : ℕ} (a : ℝ) (x t : Euclidean d) :
    gaussianFactor a x * gaussianFactor a (t + x) =
      gaussianFactor (a / 2) t * gaussianFactor (2 * a) (x + (1 / 2 : ℝ) • t) := by
  unfold gaussianFactor
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), real_inner_smul_right,
    real_inner_comm t x]
  ring

/-- The overlap integral retains the exact positive normalization constant. -/
lemma integral_gaussianFactor_overlap {d : ℕ} (a : ℝ) (t : Euclidean d) :
    (∫ x : Euclidean d, gaussianFactor a x * gaussianFactor a (t + x)) =
      gaussianFactor (a / 2) t * ∫ x : Euclidean d, gaussianFactor (2 * a) x := by
  simp_rw [gaussianFactor_overlap]
  rw [integral_const_mul, integral_add_right_eq_self]

/-- A Gaussian-weighted integral of a continuous positive-definite function
has nonnegative real part. -/
lemma positiveDefinite_gaussian_integral {d : ℕ} {f : Euclidean d → ℂ}
    (hf : PositiveDefiniteContinuity.Spec.PositiveDefinite f) (hc : Continuous f)
    {a : ℝ} (ha : 0 < a) :
    0 ≤ ∫ t : Euclidean d, gaussianFactor (a / 2) t * (f t).re := by
  let μ : Measure (Euclidean d) :=
    volume.withDensity (fun x => ENNReal.ofReal (gaussianFactor a x))
  have hg := integrable_gaussianFactor (d := d) ha
  have hgm : Measurable (fun x : Euclidean d => ENNReal.ofReal (gaussianFactor a x)) :=
    (continuous_gaussianFactor a).measurable.ennreal_ofReal
  have hfin : IsFiniteMeasure μ := by
    apply isFiniteMeasure_withDensity
    rw [← ofReal_integral_eq_lintegral_ofReal hg
      (Filter.Eventually.of_forall (fun x => (gaussianFactor_pos a x).le))]
    exact ENNReal.ofReal_ne_top
  have ht := positiveDefinite_finite_integral hf hc μ
  dsimp only [μ] at ht
  rw [prod_withDensity hgm hgm] at ht
  have hm2 : AEMeasurable (fun p : Euclidean d × Euclidean d =>
      ENNReal.ofReal (gaussianFactor a p.1) * ENNReal.ofReal (gaussianFactor a p.2))
      (volume.prod volume) :=
    ((hgm.comp measurable_fst).mul (hgm.comp measurable_snd)).aemeasurable
  rw [integral_withDensity_eq_integral_toReal_smul₀ hm2
    (Filter.Eventually.of_forall (fun p => by finiteness))] at ht
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (gaussianFactor_pos a _).le,
    smul_eq_mul] at ht
  let F : Euclidean d × Euclidean d → ℝ := fun p =>
    gaussianFactor a p.1 * gaussianFactor a p.2 * (f (p.2 - p.1)).re
  have hFi : Integrable F (volume.prod volume) := by
    apply ((hg.mul_prod hg).mul_const (f 0).re).mono'
      (by dsimp [F]; fun_prop)
    filter_upwards [] with p
    dsimp [F]
    rw [abs_mul, abs_of_pos
      (mul_pos (gaussianFactor_pos a p.1) (gaussianFactor_pos a p.2))]
    exact mul_le_mul_of_nonneg_left
      ((Complex.abs_re_le_norm _).trans (norm_le_value_zero hf _))
      (mul_pos (gaussianFactor_pos a p.1) (gaussianFactor_pos a p.2)).le
  have hpres := measurePreserving_prod_add_right
    (volume : Measure (Euclidean d)) (volume : Measure (Euclidean d))
  have htrans := hpres.integrable_comp_of_integrable hFi
  have he : (∫ p, F p ∂volume.prod volume) =
      ∫ p : Euclidean d × Euclidean d,
        gaussianFactor a p.1 * gaussianFactor a (p.2 + p.1) * (f p.2).re
        ∂volume.prod volume := by
    have heq := integral_map hpres.measurable.aemeasurable
      (hFi.aestronglyMeasurable.mono_measure (by rw [hpres.map_eq]))
    rw [hpres.map_eq] at heq
    simpa [F] using heq
  change 0 ≤ ∫ p, F p ∂volume.prod volume at ht
  rw [he] at ht
  have hI : Integrable (fun p : Euclidean d × Euclidean d =>
      gaussianFactor a p.1 * gaussianFactor a (p.2 + p.1) * (f p.2).re)
      (volume.prod volume) := by simpa [F, Function.comp_def] using htrans
  rw [integral_prod _ hI, integral_integral_swap hI] at ht
  simp_rw [integral_mul_const, integral_gaussianFactor_overlap] at ht
  have heq (t : Euclidean d) :
      (gaussianFactor (a / 2) t * ∫ x : Euclidean d, gaussianFactor (2 * a) x) * (f t).re =
      (∫ x : Euclidean d, gaussianFactor (2 * a) x) *
        (gaussianFactor (a / 2) t * (f t).re) := by ring
  simp_rw [heq, integral_const_mul] at ht
  have hpos : 0 < ∫ x : Euclidean d, gaussianFactor (2 * a) x :=
    integral_exp_pos (integrable_gaussianFactor (by positivity))
  exact (mul_nonneg_iff_of_pos_left hpos).mp ht

/-- The integral of an integrable continuous positive-definite function has
nonnegative real part, by letting its Gaussian weight increase to one. -/
lemma positiveDefinite_integral_nonneg {d : ℕ} {f : Euclidean d → ℂ}
    (hf : PositiveDefiniteContinuity.Spec.PositiveDefinite f) (hc : Continuous f)
    (hi : Integrable f) : 0 ≤ (∫ x, f x).re := by
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    (Real.tendsto_integral_cexp_sq_smul hi)
  apply ge_of_tendsto ht
  filter_upwards [Filter.Ioi_mem_atTop (0 : ℝ)] with c (hc' : 0 < c)
  have hp := positiveDefinite_gaussian_integral hf hc
    (show 0 < 2 / (Real.pi * c) by positivity)
  have hint : Integrable (fun x : Euclidean d =>
      Complex.exp (-((c : ℂ)⁻¹) * ‖x‖ ^ 2) * f x) := by
    have hg : Integrable (fun x : Euclidean d =>
        Complex.exp (-((c : ℂ)⁻¹) * ‖x‖ ^ 2)) := by
      simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
        (V := Euclidean d) (b := (c : ℂ)⁻¹) (by simpa using inv_pos.mpr hc') 0 0
    exact hg.mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall (norm_le_value_zero hf))
  have he (x : Euclidean d) :
      gaussianFactor (2 / (Real.pi * c) / 2) x = Real.exp (-c⁻¹ * ‖x‖ ^ 2) := by
    unfold gaussianFactor
    congr 1
    field_simp
  simp_rw [he] at hp
  simp only [Function.comp_apply, Complex.ofReal_inv, smul_eq_mul]
  change 0 ≤ (∫ x : Euclidean d,
    Complex.exp (-((c : ℂ)⁻¹) * ‖x‖ ^ 2) * f x).re
  calc
    0 ≤ ∫ x : Euclidean d, Real.exp (-c⁻¹ * ‖x‖ ^ 2) * (f x).re := hp
    _ = ∫ x : Euclidean d, (Complex.exp (-((c : ℂ)⁻¹) * ‖x‖ ^ 2) * f x).re := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [← Complex.ofReal_inv, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
        ← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    _ = _ := integral_re hint

/-- All-dimensional Fourier positivity, obtained by twisting by a character. -/
lemma positiveDefinite_fourier_nonneg {d : ℕ} {f : Euclidean d → ℂ}
    (hf : PositiveDefiniteContinuity.Spec.PositiveDefinite f) (hc : Continuous f)
    (hi : Integrable f) (ξ : Euclidean d) :
    0 ≤ (integralFourier f ξ).re := by
  let g : Euclidean d → ℂ := fun x => f x * character x (-ξ)
  have hgp : PositiveDefiniteContinuity.Spec.PositiveDefinite g :=
    positiveDefinite_character_mul hf (fun x y => character_conj_mul x y (-ξ))
  have hgc : Continuous g := by dsimp [g, character]; fun_prop
  have hgi : Integrable g :=
    hi.mul_bdd (by dsimp [character]; fun_prop)
      (Filter.Eventually.of_forall (fun x => (norm_character x (-ξ)).le))
  have heq : integralFourier f ξ = ∫ x, g x := by
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [g, character]
    rw [mul_comm (f x)]
    congr 2
    simp only [inner_neg_right, Complex.ofReal_neg]
    ring
  rw [heq]
  exact positiveDefinite_integral_nonneg hgp hgc hgi

theorem fourier_nonnegative : Spec.FourierNonnegative := by
  intro d φ hφ hc ε hε ξ
  exact ⟨fourier_im_eq_zero (positiveDefinite_damped hφ hε) ξ,
    positiveDefinite_fourier_nonneg (positiveDefinite_damped hφ hε)
      (damping_continuous d φ hφ hc ε) (damping_integrable d φ hφ hc ε hε) ξ⟩

theorem fourier_mass : Spec.FourierMass := by
  intro d φ hφ hc ε hε
  have hpos := fourier_nonnegative d φ hφ hc ε hε
  have hi : Integrable (density φ ε) := by
    rw [density, integralFourier_eq_native]
    apply integrable_fourier_of_nonnegative (damping_integrable d φ hφ hc ε hε)
      (damping_continuous d φ hφ hc ε).continuousAt
    · intro ξ
      simpa only [density, integralFourier_eq_native] using (hpos ξ).1
    · intro ξ
      simpa only [density, integralFourier_eq_native] using (hpos ξ).2
  exact ⟨hi, integral_density_of_integrable hφ hc hε hi⟩

theorem representation : Spec.Representation := by
  intro d φ hφ hc ε hε
  have hi := (fourier_mass d φ hφ hc ε hε).1
  have hr := fun ξ => (fourier_nonnegative d φ hφ hc ε hε ξ).1
  have hp := fun ξ => (fourier_nonnegative d φ hφ hc ε hε ξ).2
  exact ⟨densityMeasure_finite hi hp, densityMeasure_regular hi hp,
    densityMeasure_mass hφ hc hε hi hp,
    representation_of_fourier_properties hφ hc hε hi hr hp⟩

end ExpandedFA.PartIV.BochnerGaussian
