import MathGenome.Internal.FourierSobolev.P102.Periodic.Foundation
import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.OscillatoryDecay
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Topology.Instances.ZMultiples

/-! Riemann–Lebesgue decay on bounded intervals and on every positive-period
circle. No Fourier series convergence is used. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Real

namespace P102.Periodic

/-- Convert Mathlib's `exp(-2πivw)` convention to `exp(iwv)`. The statement
also holds for nonintegrable functions because the Bochner integral is totalized. -/
theorem integral_exp_mul_tendsto_cocompact (h : ℝ → ℂ) :
    Tendsto (fun w : ℝ => ∫ v : ℝ, h v * Complex.exp (Complex.I * w * v))
      (cocompact ℝ) (𝓝 0) := by
  have hc : Tendsto (fun w : ℝ => -(2 * Real.pi)⁻¹ * w)
      (cocompact ℝ) (cocompact ℝ) :=
    (Homeomorph.mulLeft₀ _
      (neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)))).toCocompactMap.cocompact_tendsto'
  have ht := (Real.tendsto_integral_exp_smul_cocompact h).comp hc
  convert ht using 1
  ext w
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  rw [mul_comm (h v)]
  congr 2
  push_cast
  field_simp

/-- Zero extension turns an integral on a measurable set into a Fourier integral
on the real line. This also holds for totalized integrals without integrability. -/
theorem setIntegral_exp_mul_tendsto_cocompact (s : Set ℝ) (hs : MeasurableSet s)
    (h : ℝ → ℂ) :
    Tendsto (fun w : ℝ => ∫ v in s, h v * Complex.exp (Complex.I * w * v))
      (cocompact ℝ) (𝓝 0) := by
  have ht := integral_exp_mul_tendsto_cocompact (s.indicator h)
  convert ht using 1
  ext w
  rw [← integral_indicator hs]
  congr 1
  ext v
  exact s.indicator_mul_left _ _

/-- Riemann–Lebesgue for arbitrary complex L¹ functions on a bounded interval. -/
theorem interval_oscillatory_decay (a b : ℝ) (h : ℝ → ℂ)
    (_hh : IntegrableOn h (Icc a b)) :
    Tendsto (fun w : ℝ => ∫ v in Icc a b, h v * Complex.exp (Complex.I * w * v))
      (comap (fun w : ℝ => |w|) atTop) (𝓝 0) := by
  have heq : comap (fun w : ℝ => |w|) atTop = cocompact ℝ := by
    rw [← comap_dist_left_atTop_eq_cocompact (0 : ℝ)]
    congr 1
    funext x
    simp [Real.dist_eq]
  rw [heq]
  exact setIntegral_exp_mul_tendsto_cocompact _ measurableSet_Icc h

/-- Explicit positive and negative half-integer specializations. -/
theorem half_integer_oscillatory_decay (h : ℝ → ℂ)
    (hh : IntegrableOn h (Icc (-Real.pi) Real.pi)) :
    Tendsto (fun N : ℕ => ∫ v in Icc (-Real.pi) Real.pi,
      h v * Complex.exp (Complex.I * ((N : ℝ) + 1 / 2) * v)) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => ∫ v in Icc (-Real.pi) Real.pi,
      h v * Complex.exp (Complex.I * (-((N : ℝ) + 1 / 2)) * v)) atTop (𝓝 0) := by
  have ht := interval_oscillatory_decay (-Real.pi) Real.pi h hh
  have hp : Tendsto (fun N : ℕ => (N : ℝ) + 1 / 2) atTop atTop :=
    tendsto_atTop_add_const_right (atTop : Filter ℕ) (1 / 2 : ℝ)
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hnonneg (N : ℕ) : 0 ≤ (N : ℝ) + 1 / 2 := by positivity
  have hp' : Tendsto (fun N : ℕ => (N : ℝ) + 1 / 2) atTop
      (comap (fun w : ℝ => |w|) atTop) := by
    rw [tendsto_comap_iff]
    change Tendsto (fun N : ℕ => |(N : ℝ) + 1 / 2|) atTop atTop
    convert hp using 1
    funext N
    exact abs_of_nonneg (hnonneg N)
  have hn' : Tendsto (fun N : ℕ => -((N : ℝ) + 1 / 2)) atTop
      (comap (fun w : ℝ => |w|) atTop) := by
    rw [tendsto_comap_iff]
    change Tendsto (fun N : ℕ => |-((N : ℝ) + 1 / 2)|) atTop atTop
    convert hp using 1
    funext N
    rw [abs_neg, abs_of_nonneg (hnonneg N)]
  constructor
  · simpa only [Function.comp_def, Complex.ofReal_add, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat] using ht.comp hp'
  · simpa only [Function.comp_def, Complex.ofReal_neg, Complex.ofReal_add,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using ht.comp hn' 

/-- Periodic Riemann–Lebesgue, for an integrable representative and normalized Haar. -/
theorem coefficient_decay (T : ℝ) [hT : Fact (0 < T)] (f : Circle T → ℂ)
    (hf : Integrable f (haar T)) :
    Tendsto (coefficient T f) cofinite (𝓝 0) := by
  have hscaled : Integrable (fun t : ℝ => f (t : Circle T))
      (ENNReal.ofReal T⁻¹ • volume.restrict (Ioc 0 (0 + T))) :=
    ((interval_measure T 0).integrable_comp hf.aestronglyMeasurable).mpr hf
  have hioc : IntegrableOn (fun t : ℝ => f (t : Circle T)) (Ioc 0 T) := by
    change Integrable (fun t : ℝ => f (t : Circle T)) (volume.restrict (Ioc 0 T))
    simpa only [zero_add] using
      (integrable_smul_measure (by simp [hT.out]) ENNReal.ofReal_ne_top).mp hscaled
  have hicc : IntegrableOn (fun t : ℝ => f (t : Circle T)) (Icc 0 T) :=
    (integrableOn_Icc_iff_integrableOn_Ioc (by finiteness)).mpr hioc
  have ht := interval_oscillatory_decay 0 T (fun t : ℝ => f (t : Circle T)) hicc
  have heq : comap (fun w : ℝ => |w|) atTop = cocompact ℝ := by
    rw [← comap_dist_left_atTop_eq_cocompact (0 : ℝ)]
    congr 1
    funext x
    simp [Real.dist_eq]
  rw [heq] at ht
  have hc : Tendsto (fun k : ℤ => -(2 * Real.pi / T) * (k : ℝ))
      cofinite (cocompact ℝ) :=
    (show Tendsto (fun x : ℝ => -(2 * Real.pi / T) * x)
      (cocompact ℝ) (cocompact ℝ) from
        (Homeomorph.mulLeft₀ _ (neg_ne_zero.mpr
          (div_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hT.out.ne'))).toCocompactMap.cocompact_tendsto').comp Int.tendsto_coe_cofinite
  have hz := (ht.comp hc).const_smul (1 / T : ℝ)
  simp only [smul_zero] at hz
  convert hz using 1
  ext k
  rw [coefficient_interval T f k 0, zero_add,
    intervalIntegral.integral_of_le hT.out.le, ← integral_Icc_eq_integral_Ioc]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  push_cast
  congr 2
  ring

/-- The representative theorem descends to the canonical L¹ quotient. -/
theorem coefficientL1_decay (T : ℝ) [Fact (0 < T)] (f : L1 T) :
    Tendsto (coefficientL1 T f) cofinite (𝓝 0) := by
  exact coefficient_decay T f (MeasureTheory.L1.integrable_coeFn f)

end P102.Periodic
