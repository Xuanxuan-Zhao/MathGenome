import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.NormalizationBridge
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.PeriodicIntegral
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.Representation

noncomputable section
namespace SingleVariableAnalysis
open Riemann
open scoped BigOperators
namespace FourierNormalization
abbrev periodMode := Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.periodModeValue

/-- Positive linear substitution for proper complex Darboux integrals. -/
theorem integral_comp_pos_mul {f : ℝ → ℂ} {a b k : ℝ} (hk : 0 < k)
    (hf : ComplexIntegrable f (k*a) (k*b)) :
    ∃ hg : ComplexIntegrable (fun t => f (k*t)) a b,
      (k : ℂ) * complexIntegral _ hg = complexIntegral f hf := by
  have hab : a ≤ b := (mul_le_mul_iff_right₀ hk).mp (RealIntegrable.ordered hf.1)
  have hφ : C1OnInterval (fun t => k*t) (fun _ => k) a b :=
    ⟨continuousOn_const, fun _ _ => (hasDerivAt_const_mul k).hasDerivWithinAt⟩
  have hfo : OrientedComplexIntegrable f (k*a) (k*b) := by
    simpa only [O.complexIntegrableValue, min_eq_left (RealIntegrable.ordered hf.1),
      max_eq_right (RealIntegrable.ordered hf.1)] using hf
  obtain ⟨hw, hv⟩ := complex_monotone_substitution (fun t => k*t) (fun _ => k) f
    hab hφ (Or.inl (by intro x hx y hy hxy; exact mul_le_mul_of_nonneg_left hxy hk.le)) hfo
  have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
  obtain ⟨hg, he⟩ := complex_mul_value hw (k : ℂ)⁻¹
  simp only [← mul_assoc, inv_mul_cancel₀ hkC, one_mul] at hg he
  refine ⟨hg, ?_⟩
  rw [he, ← mul_assoc, mul_inv_cancel₀ hkC, one_mul]
  exact hv.trans (oriented_complex_agreement f (RealIntegrable.ordered hf.1) hfo hf)

theorem mode_add (T : ℝ) (n : ℤ) (x y : ℝ) : periodMode T n (x+y) = periodMode T n x * periodMode T n y := by
  unfold periodMode Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.periodModeValue
    Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.modeValue
  rw [show ((2 * Real.pi * (x+y) / T : ℝ) : ℂ) =
    ((2 * Real.pi * x / T : ℝ) : ℂ) + ((2 * Real.pi * y / T : ℝ) : ℂ) by push_cast; ring]
  rw [mul_add, mul_add, Complex.exp_add]

theorem mode_periodic {T : ℝ} (hT : 0 < T) (n : ℤ) : Function.Periodic (periodMode T n) T := by
  intro x
  rw [mode_add]
  have h : periodMode T n T = 1 := by
    unfold periodMode Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.periodModeValue
      Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.modeValue
    rw [mul_div_cancel_right₀ _ hT.ne']
    rw [show Complex.I * ((n : ℂ) * ((2*Real.pi : ℝ) : ℂ)) =
      (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  rw [h, mul_one]

theorem mode_continuous (T : ℝ) (n : ℤ) : Continuous (periodMode T n) := by
  unfold periodMode Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.periodModeValue
    Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.modeValue
  fun_prop

theorem mode_scaled {T : ℝ} (hT : 0 < T) (n : ℤ) (t : ℝ) :
    periodMode T n (T*t/(2*Real.pi)) = fourierMode n t := by
  unfold periodMode Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.periodModeValue
  congr 1
  field_simp

theorem mode_opposite (T : ℝ) (n : ℤ) (x : ℝ) : periodMode T n x * periodMode T (-n) x = 1 := by
  unfold periodMode Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.periodModeValue
    Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.modeValue
  rw [← Complex.exp_add]
  push_cast
  rw [show Complex.I * ((n : ℂ) * (2*(Real.pi : ℂ)*(x : ℂ)/(T : ℂ))) +
      Complex.I * (-(n : ℂ) * (2*(Real.pi : ℂ)*(x : ℂ)/(T : ℂ))) = 0 by ring,
    Complex.exp_zero]

theorem weighted_periodic {f : ℝ → ℂ} {T : ℝ} (hT : 0 < T)
    (hp : Function.Periodic f T) (n : ℤ) :
    Function.Periodic (fun x => f x * periodMode T (-n) x) T := by
  intro x
  change f (x+T) * periodMode T (-n) (x+T) = f x * periodMode T (-n) x
  rw [hp x, mode_periodic hT (-n) x]

theorem weighted_integrable {f : ℝ → ℂ} {T b : ℝ} (hT : 0 < T)
    (hp : Function.Periodic f T) (hf : ComplexIntegrable f b (b+T))
    (a : ℝ) (n : ℤ) : ComplexIntegrable (fun x => f x * periodMode T (-n) x) a (a+T) := by
  obtain ⟨ha, _⟩ := complex_integral_period hT hp hf a
  exact complex_product ha (Fourier.complexIntegrable_of_continuousOn
    (by linarith) (mode_continuous T (-n)).continuousOn)

theorem scaled_endpoint (T : ℝ) :
    T/(2*Real.pi)*Real.pi = T/(2*Real.pi)*(-Real.pi)+T := by
  field_simp
  ring

theorem rescale_periodic {f : ℝ → ℂ} {T : ℝ} (hp : Function.Periodic f T) :
    Function.Periodic (Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.rescaleValue f T)
      (2*Real.pi) := by
  intro t
  change f (T*(t+2*Real.pi)/(2*Real.pi)) = f (T*t/(2*Real.pi))
  rw [show T*(t+2*Real.pi)/(2*Real.pi) = T*t/(2*Real.pi)+T by
    field_simp]
  exact hp _

/-- Substitution followed by transport of the integration interval. -/
theorem rescale_integral {f : ℝ → ℂ} {T b : ℝ} (hT : 0 < T)
    (hp : Function.Periodic f T) (hf : ComplexIntegrable f b (b+T)) :
    ∃ hg : ComplexIntegrable
      (Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.rescaleValue f T)
      (-Real.pi) Real.pi,
      ((T/(2*Real.pi) : ℝ) : ℂ) * complexIntegral _ hg = complexIntegral f hf := by
  let k := T/(2*Real.pi)
  have hk : 0 < k := div_pos hT (by positivity)
  obtain ⟨hm, hmv⟩ := complex_integral_period hT hp hf (k*(-Real.pi))
  have he : k*Real.pi = k*(-Real.pi)+T := scaled_endpoint T
  have hf' : ComplexIntegrable f (k*(-Real.pi)) (k*Real.pi) := by rw [he]; exact hm
  obtain ⟨hg, hgv⟩ := integral_comp_pos_mul hk hf'
  have hfun : (fun t => f (k*t)) =
      Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.rescaleValue f T := by
    funext t
    dsimp [k, Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.rescaleValue]
    congr 1
    ring
  simp only [hfun] at hg hgv
  refine ⟨hg, hgv.trans ?_⟩
  exact (complexIntegral_congr_endpoints hf' hm rfl he).trans hmv

end FourierNormalization

abbrev periodFourierMode := Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.periodModeValue
abbrev rescaleFourier := Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.rescaleValue
abbrev periodFourierCoeff := Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.periodCoefficientValue
abbrev periodFourierPartialSum := Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.periodPartialSumValue

open FourierNormalization

theorem periodFourier_real_input :
    Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.realInputBridge := by
  intro f T b hT hp hf
  exact ⟨hp.comp Complex.ofReal, hf,
    (real_zero_value (by linarith : b ≤ b+T)).choose⟩

theorem periodFourierCoeff_integrable :
    Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.weightedIntegrability := by
  intro f T b hT hp hf a n
  exact weighted_integrable hT hp hf a n

theorem periodFourierCoeff_origin :
    Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.originIndependence := by
  intro f T hT hp a b n ha hb
  obtain ⟨ha', he⟩ := complex_integral_period hT (weighted_periodic hT hp n) hb a
  exact congrArg (fun z : ℂ => ((T⁻¹ : ℝ) : ℂ)*z) he

theorem rescaleFourier_integrable :
    Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.rescaledIntegrability := by
  intro f T b hT hp hf
  exact ⟨rescale_periodic hp, (rescale_integral hT hp hf).choose⟩

theorem fourierCoeff_rescale :
    Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.coefficientRescaling := by
  intro f T b hT hp hf a n hg ha
  obtain ⟨hj, hjv⟩ := rescale_integral hT (weighted_periodic hT hp n) ha
  have hfun : rescaleFourier (fun x => f x * periodMode T (-n) x) T =
      (fun t => rescaleFourier f T t * fourierMode (-n) t) := by
    funext t
    exact congrArg (fun z => f (T*t/(2*Real.pi))*z) (mode_scaled hT (-n) t)
  dsimp only [rescaleFourier] at hfun
  simp only [hfun] at hj hjv
  change ((1/(2*Real.pi) : ℝ) : ℂ)*complexIntegral _ hg =
    ((T⁻¹ : ℝ) : ℂ)*complexIntegral _ ha
  rw [← hjv]
  push_cast
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  field_simp

theorem periodFourierCoeff_translate :
    Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.translationPhase := by
  intro f T b hT hp hf c a d n
  have hd := weighted_integrable hT hp hf d n
  obtain ⟨ht, htv⟩ := complex_periodic_translate hT (weighted_periodic hT hp n) hd a c
  obtain ⟨hc, hcv⟩ := complex_mul_value ht (periodMode T n c)
  have hfun : (fun x => periodMode T n c * (f (x+c) * periodMode T (-n) (x+c))) =
      (fun x => f (x+c) * periodMode T (-n) x) := by
    funext x
    rw [mode_add]
    calc
      _ = (f (x+c)*periodMode T (-n) x) * (periodMode T n c*periodMode T (-n) c) := by ring
      _ = _ := by rw [mode_opposite, mul_one]
  simp only [hfun] at hc hcv
  refine ⟨hc, fun hd' => ?_⟩
  change ((T⁻¹ : ℝ) : ℂ)*complexIntegral _ hc =
    periodMode T n c * (((T⁻¹ : ℝ) : ℂ)*complexIntegral _ hd')
  have htv' : complexIntegral _ ht = complexIntegral _ hd := htv
  rw [hcv, htv']
  ring

theorem periodFourierPartialSum_rescale :
    Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.partialSumRescaling := by
  intro f T b hT hp hf a h hg N t
  unfold Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.partialSumValue
    Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.periodPartialSumValue
  apply Finset.sum_congr rfl
  intro n hn
  rw [fourierCoeff_rescale f T b hT hp hf a n (hg n) (h n)]
  exact congrArg (fun z => periodFourierCoeff f T a n (h n) * z) (mode_scaled hT n t).symm

theorem fourier_pointwise_convergence_rescale :
    Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.pointwiseConvergenceTransfer := by
  intro f T b hT hp hf a h hg t L
  have he : (fun N => fourierPartialSum (rescaleFourier f T) hg N t) =
      (fun N => periodFourierPartialSum f T a h N (T*t/(2*Real.pi))) := by
    funext N
    exact periodFourierPartialSum_rescale f T b hT hp hf a h hg N t
  rw [he]

theorem fourier_uniform_convergence_rescale :
    Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.uniformConvergenceTransfer := by
  intro f T b hT hp hf a h hg F
  have he (N : ℕ) (t : ℝ) :=
    periodFourierPartialSum_rescale f T b hT hp hf a h hg N t
  constructor
  · intro hu
    have hu' := hu.comp (fun x => 2*Real.pi*x/T)
    have hinv (x : ℝ) : T*(2*Real.pi*x/T)/(2*Real.pi) = x := by
      field_simp
    simpa only [he, Function.comp_def,
      Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.rescaleValue, hinv] using hu'
  · intro hu
    have hu' := hu.comp (fun t => T*t/(2*Real.pi))
    have hF : Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.rescaleValue F T =
        (fun t => F (T*t/(2*Real.pi))) := rfl
    rw [hF]
    simpa only [Function.comp_def, ← he] using hu'

theorem fourier_normalization_real_representations :
    Specs.SingleVariableAnalysis.Ch19.NormalizationBridge.realRepresentations :=
  ⟨fourierCoeff_zero_real, fourierCoeff_positive_real, fourierCoeff_negative_real,
    fourierPartialSum_real⟩

end SingleVariableAnalysis

