import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.CoefficientDecay
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.RiemannLebesgue
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.Parts
import Mathlib.Analysis.Calculus.TangentCone.Real
import Batteries.Tactic.OpenPrivate

noncomputable section
namespace SingleVariableAnalysis
open Riemann Set
open private complexIntegral_congr realIntegral_congr phase_norm
  from MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch17.OscillatoryBound

namespace Fourier

/-- Integer modes have identical values at the two ends of a period. -/
theorem mode_endpoints (n : ℤ) : fourierMode n (-Real.pi) = fourierMode n Real.pi := by
  have h := Complex.exp_int_mul_two_pi_mul_I n
  have he : Complex.I * ((n : ℂ) * (Real.pi : ℂ)) =
      Complex.I * ((n : ℂ) * ((-Real.pi : ℝ) : ℂ)) +
        (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  change Complex.exp _ = Complex.exp _
  rw [he, Complex.exp_add, h, mul_one]

/-- One integration by parts, requiring matching values only for the amplitude. -/
theorem coefficient_derivative {f df : ℝ → ℂ}
    (hc : ContinuousOn f (Icc (-Real.pi) Real.pi))
    (hd : ∀ x ∈ Ioo (-Real.pi) Real.pi, HasDerivAt f (df x) x)
    (hdi : ComplexIntegrable df (-Real.pi) Real.pi)
    (hend : f (-Real.pi) = f Real.pi)
    (Hf : ∀ n : ℤ, ComplexIntegrable (fun x => f x * fourierMode (-n) x)
      (-Real.pi) Real.pi)
    (Hd : ∀ n : ℤ, ComplexIntegrable (fun x => df x * fourierMode (-n) x)
      (-Real.pi) Real.pi) (n : ℤ) :
    fourierCoeff df n (Hd n) = (Complex.I * (n : ℂ)) * fourierCoeff f n (Hf n) := by
  let e := fourierMode (-n)
  let c : ℂ := -(Complex.I * (n : ℂ))
  have hed (x : ℝ) : HasDerivAt e (c * e x) x := by
    change HasDerivAt (fun t : ℝ => Complex.exp
      (Complex.I * (((-n : ℤ) : ℂ) * (t : ℂ)))) (c * e x) x
    simpa [e, c, fourierMode, Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.modeValue,
      mul_assoc] using oscillatory_phase_hasDerivAt (-(n : ℝ)) x
  have hec : ContinuousOn e (Icc (-Real.pi) Real.pi) :=
    (continuous_iff_continuousAt.mpr (fun x => (hed x).continuousAt)).continuousOn
  have hei := complexIntegrable_of_continuousOn (by linarith [Real.pi_pos]) hec
  obtain ⟨hcei, _⟩ := complex_mul_value hei c
  obtain ⟨hcefi, hcefv⟩ := complex_mul_value (Hf n) c
  obtain ⟨h₁, h₂, hp⟩ := complex_parts f e df (fun x => c * e x)
    (-Real.pi) Real.pi (by linarith [Real.pi_pos]) hc hec hd
    (fun x _ => hed x) hdi hcei
  change complexIntegral _ h₁ = f Real.pi * e Real.pi -
    f (-Real.pi) * e (-Real.pi) - complexIntegral _ h₂ at hp
  have heend : e (-Real.pi) = e Real.pi := mode_endpoints (-n)
  rw [hend, heend, sub_self, zero_sub] at hp
  have hfun : (fun x => f x * (c * e x)) =
      (fun x => c * (f x * fourierMode (-n) x)) := by funext x; dsimp [e]; ring
  have hv : complexIntegral _ h₁ = c * complexIntegral _ (Hf n) :=
    (complexIntegral_congr h₁ hcefi hfun).trans hcefv
  have hdv : complexIntegral _ h₂ = complexIntegral _ (Hd n) := rfl
  rw [hv, hdv] at hp
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegral _ (Hd n) =
    (Complex.I * (n : ℂ)) *
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegral _ (Hf n))
  have hi : complexIntegral _ (Hd n) = -c * complexIntegral _ (Hf n) := by
    calc
      _ = -(c * complexIntegral _ (Hf n)) := by rw [hp]; ring
      _ = _ := by ring
  rw [hi]
  dsimp [c]
  ring

/-- The normalization and unit modulus give the exact coefficient L¹ bound. -/
theorem coefficient_norm_bound {f : ℝ → ℂ}
    (H : ∀ n : ℤ, ComplexIntegrable (fun x => f x * fourierMode (-n) x)
      (-Real.pi) Real.pi)
    (hn : RealIntegrable (fun x => ‖f x‖) (-Real.pi) Real.pi) (n : ℤ) :
    ‖fourierCoeff f n (H n)‖ ≤
      (1 / (2 * Real.pi)) * realIntegral _ hn := by
  obtain ⟨hw, hb, _⟩ := complex_norm_estimate _ (H n)
  have hmode (x : ℝ) : ‖fourierMode (-n) x‖ = 1 := by
    simpa [fourierMode, Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.modeValue,
      mul_assoc] using phase_norm (-(n : ℝ)) x
  have he : (fun x => ‖f x * fourierMode (-n) x‖) = (fun x => ‖f x‖) := by
    funext x; rw [norm_mul, hmode, mul_one]
  have hb' : ‖complexIntegral _ (H n)‖ ≤ realIntegral _ hn :=
    hb.trans_eq (realIntegral_congr hw hn he)
  have hα : ‖(((1 / (2 * Real.pi)) : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  change ‖(((1 / (2 * Real.pi)) : ℝ) : ℂ) * complexIntegral _ (H n)‖ ≤ _
  rw [norm_mul, hα]
  exact mul_le_mul_of_nonneg_left hb' (by positivity)

end Fourier

/-- Differentiation of Fourier coefficients, the quantitative bound, and
little-o decay, for precisely the lower-order endpoint matching hypotheses. -/
theorem fourierCoeff_derivative_decay :
    Specs.SingleVariableAnalysis.Ch19.CoefficientDecay.derivativeDecay := by
  intro f k hk hf hend
  let S := Icc (-Real.pi) Real.pi
  let D (j : ℕ) := iteratedDerivWithin j f S
  have hu : UniqueDiffOn ℝ S := uniqueDiffOn_Icc (by linarith [Real.pi_pos])
  have hreg := (contDiffOn_nat_iff_continuousOn_differentiableOn_deriv hu).mp hf
  have hcont (j : ℕ) (hj : j ≤ k) : ContinuousOn (D j) S := hreg.1 j hj
  have hdi (j : ℕ) (hj : j ≤ k) : ComplexIntegrable (D j) (-Real.pi) Real.pi :=
    Fourier.complexIntegrable_of_continuousOn (by linarith [Real.pi_pos]) (hcont j hj)
  let H (j : ℕ) (hj : j ≤ k) := fourierCoeff_integrable (D j) (hdi j hj)
  have H₀ : ∀ n : ℤ, ComplexIntegrable (fun x => f x * fourierMode (-n) x)
      (-Real.pi) Real.pi := by
    simpa only [D, iteratedDerivWithin_zero] using H 0 (Nat.zero_le k)
  have hformula (j : ℕ) (hj : j ≤ k) (n : ℤ) :
      fourierCoeff (D j) n (H j hj n) =
        (Complex.I * (n : ℂ)) ^ j * fourierCoeff f n (H₀ n) := by
    induction j with
    | zero => simp only [D, iteratedDerivWithin_zero, pow_zero, one_mul]
    | succ j ih =>
      have hjk : j < k := lt_of_lt_of_le (Nat.lt_succ_self j) hj
      have hd (x : ℝ) (hx : x ∈ Ioo (-Real.pi) Real.pi) :
          HasDerivAt (D j) (D (j + 1) x) x := by
        have hdw := (hreg.2 j hjk x ⟨hx.1.le, hx.2.le⟩).hasDerivWithinAt
        have hd' := hdw.hasDerivAt (Icc_mem_nhds hx.1 hx.2)
        simpa only [D, iteratedDerivWithin_succ] using hd'
      have hs := Fourier.coefficient_derivative (hcont j hjk.le) hd (hdi (j+1) hj)
        (hend j hjk) (H j hjk.le) (H (j+1) hj) n
      rw [hs, ih hjk.le, pow_succ]
      ring
  have hformulaK := hformula k le_rfl
  have hn : RealIntegrable (fun x => ‖D k x‖) (-Real.pi) Real.pi :=
    Fourier.realIntegrable_of_continuousOn (by linarith [Real.pi_pos])
      (hcont k le_rfl).norm
  refine ⟨H₀, H k le_rfl, hn, hformulaK, ?_, ?_⟩
  · intro n hnz
    have hnormeq : |(n : ℝ)| ^ k * ‖fourierCoeff f n (H₀ n)‖ =
        ‖fourierCoeff (D k) n (H k le_rfl n)‖ := by
      rw [hformulaK n, norm_mul, norm_pow]
      simp [Complex.norm_intCast, ← Int.cast_abs, Complex.norm_I]
    have hb := Fourier.coefficient_norm_bound (H k le_rfl) hn n
    have hnpos : 0 < |(n : ℝ)| ^ k := pow_pos (abs_pos.mpr (by exact_mod_cast hnz)) _
    have hbound : ‖fourierCoeff f n (H₀ n)‖ ≤
        ((1 / (2 * Real.pi)) * realIntegral _ hn) / |(n : ℝ)| ^ k := by
      apply (le_div_iff₀ hnpos).mpr
      rw [mul_comm, hnormeq]
      exact hb
    calc
      _ ≤ _ := hbound
      _ = (1 / (2 * Real.pi * |(n : ℝ)| ^ k)) * realIntegral _ hn := by ring
  · intro ε hε
    obtain ⟨N, hN⟩ := fourierCoeff_tendsto_zero (D k) (hdi k le_rfl) (H k le_rfl) ε hε
    refine ⟨N, fun n hnN => ?_⟩
    have hsmall := hN n hnN
    change ‖fourierCoeff (D k) n (H k le_rfl n)‖ < ε at hsmall
    rw [hformulaK n, norm_mul, norm_pow] at hsmall
    have hc : ‖Complex.I * (n : ℂ)‖ = |(n : ℝ)| := by
      simp [norm_mul, Complex.norm_intCast, ← Int.cast_abs]
    rwa [hc] at hsmall

end SingleVariableAnalysis
