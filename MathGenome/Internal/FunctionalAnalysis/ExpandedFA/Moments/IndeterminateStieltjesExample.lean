import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Moments.IndeterminateStieltjesExample
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Moments.StieltjesExistence
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert

noncomputable section
open MeasureTheory Set Real
namespace ExpandedFA.Moments.IndeterminateStieltjesExample

lemma perturbation_nonnegative (a : ℝ) (ha : a ∈ Icc (-1 : ℝ) 1) (y : ℝ) :
    0 ≤ 1 + a * sin (2 * Real.pi * y) := by
  have habs : |a| ≤ 1 := abs_le.mpr ha
  have h : |a * sin (2 * Real.pi * y)| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul habs (abs_sin_le_one _) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  linarith [(abs_le.mp h).1]

theorem density_nonnegative : Spec.DensityNonnegative := by
  intro a ha x hx
  exact mul_nonneg (div_nonneg (exp_pos _).le (mul_nonneg (sqrt_nonneg _) hx.le))
    (perturbation_nonnegative a ha (log x))

lemma integrable_gaussian : Integrable (fun y : ℝ => exp (-y ^ 2)) := by
  simpa using integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num)

lemma gaussian_sine_integrable :
    Integrable (fun y : ℝ => exp (-y ^ 2) * sin (2 * Real.pi * y)) := by
  apply integrable_gaussian.mono' (by fun_prop)
  filter_upwards [] with y
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  exact mul_le_of_le_one_right (exp_pos _).le (abs_sin_le_one _)

lemma gaussian_sine_integral :
    (∫ y : ℝ, exp (-y ^ 2) * sin (2 * Real.pi * y)) = 0 := by
  have h := integral_neg_eq_self (fun y : ℝ => exp (-y ^ 2) * sin (2 * Real.pi * y)) volume
  simp only [neg_sq, mul_neg, sin_neg, mul_neg, integral_neg] at h
  linarith

lemma gaussian_shift (n y : ℝ) :
    exp (n * (y + n / 2) - (y + n / 2) ^ 2) =
      exp (n ^ 2 / 4) * exp (-y ^ 2) := by
  rw [← exp_add]
  congr 1
  ring

lemma tilted_gaussian_integrable (n : ℝ) :
    Integrable (fun y : ℝ => exp (n * y - y ^ 2)) := by
  have h := (integrable_gaussian.const_mul (exp (n ^ 2 / 4))).comp_sub_right (n / 2)
  convert h using 1
  funext y
  rw [← exp_add]
  congr 1
  ring

lemma tilted_gaussian_integral (n : ℝ) :
    (∫ y : ℝ, exp (n * y - y ^ 2)) = exp (n ^ 2 / 4) * sqrt Real.pi := by
  rw [← integral_add_right_eq_self (fun y : ℝ => exp (n * y - y ^ 2)) (n / 2)]
  simp_rw [gaussian_shift, integral_const_mul]
  congr 1
  simpa using integral_gaussian (1 : ℝ)

lemma tilted_sine_integrable (n : ℝ) :
    Integrable (fun y : ℝ => exp (n * y - y ^ 2) * sin (2 * Real.pi * y)) := by
  apply (tilted_gaussian_integrable n).mono' (by fun_prop)
  filter_upwards [] with y
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  exact mul_le_of_le_one_right (exp_pos _).le (abs_sin_le_one _)

lemma tilted_sine_integral (n : ℕ) :
    (∫ y : ℝ, exp ((n : ℝ) * y - y ^ 2) * sin (2 * Real.pi * y)) = 0 := by
  rw [← integral_add_right_eq_self
    (fun y : ℝ => exp ((n : ℝ) * y - y ^ 2) * sin (2 * Real.pi * y)) ((n : ℝ) / 2)]
  have hs (y : ℝ) : sin (2 * Real.pi * (y + (n : ℝ) / 2)) =
      (-1 : ℝ) ^ n * sin (2 * Real.pi * y) := by
    rw [show 2 * Real.pi * (y + (n : ℝ) / 2) =
      2 * Real.pi * y + (n : ℝ) * Real.pi by ring, sin_add_nat_mul_pi]
  simp_rw [gaussian_shift, hs]
  have hf : (fun y : ℝ => exp ((n : ℝ) ^ 2 / 4) * exp (-y ^ 2) *
      ((-1 : ℝ) ^ n * sin (2 * Real.pi * y))) =
      (fun y : ℝ => (exp ((n : ℝ) ^ 2 / 4) * (-1 : ℝ) ^ n) *
        (exp (-y ^ 2) * sin (2 * Real.pi * y))) := by funext y; ring
  rw [hf, integral_const_mul, gaussian_sine_integral, mul_zero]

/-- The logarithmic form of the moment density. -/
def logKernel (a : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  exp ((n : ℝ) * y - y ^ 2) / sqrt Real.pi * (1 + a * sin (2 * Real.pi * y))

lemma logKernel_integrable (a : ℝ) (n : ℕ) : Integrable (logKernel a n) := by
  have h₁ := (tilted_gaussian_integrable (n : ℝ)).div_const (sqrt Real.pi)
  have h₂ := ((tilted_sine_integrable (n : ℝ)).div_const (sqrt Real.pi)).const_mul a
  convert h₁.add h₂ using 1
  funext y
  dsimp [logKernel]
  ring

lemma logKernel_integral (a : ℝ) (n : ℕ) :
    (∫ y : ℝ, logKernel a n y) = sequenceValue n := by
  have hf : logKernel a n = fun y : ℝ =>
      exp ((n : ℝ) * y - y ^ 2) / sqrt Real.pi +
      a * (exp ((n : ℝ) * y - y ^ 2) * sin (2 * Real.pi * y) / sqrt Real.pi) := by
    funext y; dsimp [logKernel]; ring
  rw [hf, integral_add
    ((tilted_gaussian_integrable (n : ℝ)).div_const (sqrt Real.pi))
    (((tilted_sine_integrable (n : ℝ)).div_const (sqrt Real.pi)).const_mul a),
    integral_div, integral_const_mul, integral_div,
    tilted_gaussian_integral, tilted_sine_integral]
  simp [sequenceValue, ne_of_gt (sqrt_pos.2 pi_pos)]

lemma exp_moment_density (a : ℝ) (n : ℕ) (y : ℝ) :
    exp y • (densityValue a (exp y) * exp y ^ n) = logKernel a n y := by
  have he : exp ((n : ℝ) * y - y ^ 2) = exp y ^ n * exp (-y ^ 2) := by
    rw [sub_eq_add_neg, exp_add, exp_nat_mul]
  dsimp [densityValue, logKernel]
  rw [log_exp, he]
  field_simp

lemma weighted_density_integrable (a : ℝ) (n : ℕ) :
    IntegrableOn (fun x : ℝ => densityValue a x * x ^ n) (Ioi 0) := by
  apply (integrable_comp_exp _).mp
  simpa only [exp_moment_density] using logKernel_integrable a n

lemma weighted_density_integral (a : ℝ) (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), densityValue a x * x ^ n) = sequenceValue n := by
  rw [← integral_comp_exp]
  simpa only [exp_moment_density] using logKernel_integral a n

lemma density_measurable (a : ℝ) : Measurable (densityValue a) := by
  unfold densityValue
  fun_prop

lemma density_toReal_ae (a : ℝ) (ha : a ∈ Icc (-1 : ℝ) 1) :
    (fun x => (ENNReal.ofReal (densityValue a x)).toReal) =ᵐ[volume.restrict (Ioi 0)]
      densityValue a := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact ENNReal.toReal_ofReal (density_nonnegative a ha x hx)

lemma moment_integrable (a : ℝ) (ha : a ∈ Icc (-1 : ℝ) 1) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (measureValue a) := by
  apply (integrable_withDensity_iff_integrable_smul₀'
    (density_measurable a).ennreal_ofReal.aemeasurable (by simp)).mpr
  apply (weighted_density_integrable a n).congr
  filter_upwards [density_toReal_ae a ha] with x hx
  simp [hx, smul_eq_mul]

lemma moment_integral (a : ℝ) (ha : a ∈ Icc (-1 : ℝ) 1) (n : ℕ) :
    (∫ x : ℝ, x ^ n ∂measureValue a) = sequenceValue n := by
  rw [measureValue, integral_withDensity_eq_integral_toReal_smul
    (density_measurable a).ennreal_ofReal (by simp)]
  calc
    _ = ∫ x in Ioi (0 : ℝ), densityValue a x * x ^ n := by
      apply integral_congr_ae
      filter_upwards [density_toReal_ae a ha] with x hx
      simp [hx, smul_eq_mul]
    _ = sequenceValue n := weighted_density_integral a n

lemma nonpositive_mass (a : ℝ) : measureValue a (Iic 0) = 0 := by
  apply withDensity_absolutelyContinuous _ _
  rw [Measure.restrict_apply measurableSet_Iic]
  have he : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by ext x; simp
  rw [he, measure_empty]

lemma probability_measure (a : ℝ) (ha : a ∈ Icc (-1 : ℝ) 1) :
    IsProbabilityMeasure (measureValue a) := by
  constructor
  apply (ENNReal.toReal_eq_one_iff _).mp
  have h := moment_integral a ha 0
  simpa [sequenceValue, Measure.real, smul_eq_mul] using h

theorem measure_properties : Spec.MeasureProperties := by
  intro a ha
  have := probability_measure a ha
  refine ⟨inferInstance, nonpositive_mass a, ⟨inferInstance, ?_, ?_⟩, ?_⟩
  · exact measure_mono_null Iio_subset_Iic_self (nonpositive_mass a)
  · intro n
    exact ⟨moment_integrable a ha n, moment_integral a ha n⟩
  · intro n
    simpa only [Real.norm_eq_abs, abs_pow] using (moment_integrable a ha n).norm

lemma density_continuousOn (a : ℝ) : ContinuousOn (densityValue a) (Ioi 0) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hs0 : sqrt Real.pi ≠ 0 := ne_of_gt (sqrt_pos.2 pi_pos)
  have hd0 : sqrt Real.pi * x ≠ 0 := mul_ne_zero hs0 hx0
  unfold densityValue
  apply ContinuousAt.continuousWithinAt
  fun_prop

lemma parameter_eq_of_measure_eq (a b : ℝ) (ha : a ∈ Icc (-1 : ℝ) 1)
    (hb : b ∈ Icc (-1 : ℝ) 1) (h : measureValue a = measureValue b) : a = b := by
  have he : (fun x => ENNReal.ofReal (densityValue a x)) =ᵐ[volume.restrict (Ioi 0)]
      (fun x => ENNReal.ofReal (densityValue b x)) :=
    (withDensity_eq_iff_of_sigmaFinite
      (density_measurable a).ennreal_ofReal.aemeasurable
      (density_measurable b).ennreal_ofReal.aemeasurable).mp h
  have hr : densityValue a =ᵐ[volume.restrict (Ioi 0)] densityValue b := by
    filter_upwards [he, density_toReal_ae a ha, density_toReal_ae b hb] with x he ha hb
    rw [← ha, ← hb, he]
  have hp := Measure.eqOn_open_of_ae_eq hr isOpen_Ioi
    (density_continuousOn a) (density_continuousOn b)
  have hd := hp (x := exp (1 / 4)) (exp_pos _)
  simp only [densityValue, log_exp] at hd
  have hs : 2 * Real.pi * (1 / 4) = Real.pi / 2 := by ring
  rw [hs, sin_pi_div_two, mul_one, mul_one] at hd
  have hpos : 0 < exp (-(1 / 4 : ℝ) ^ 2) / (sqrt Real.pi * exp (1 / 4)) :=
    div_pos (exp_pos _) (mul_pos (sqrt_pos.2 pi_pos) (exp_pos _))
  have := (mul_left_cancel₀ (ne_of_gt hpos)) hd
  linarith

theorem measures_distinct : Spec.Distinct := by
  intro a ha b hb hab h
  exact hab (parameter_eq_of_measure_eq a b ha hb h)

/-- Explicit nonuniqueness, together with positivity of both Stieltjes forms. -/
theorem indeterminate : Spec.Indeterminate := by
  have h₀ := (measure_properties 0 (by norm_num)).2.2.1
  have h₁ := (measure_properties 1 (by norm_num)).2.2.1
  obtain ⟨h, hs⟩ := StieltjesExistence.stieltjes_necessity sequenceValue (measureValue 0) h₀
  exact ⟨h, hs, measureValue 0, measureValue 1, h₀, h₁,
    measures_distinct 0 (by norm_num) 1 (by norm_num) (by norm_num)⟩

end ExpandedFA.Moments.IndeterminateStieltjesExample
