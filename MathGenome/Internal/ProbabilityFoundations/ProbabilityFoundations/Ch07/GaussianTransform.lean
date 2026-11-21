import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.TransformObjects
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.GaussianTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
The Gaussian identities of paper.tex:2445–2462, with the probability convention
`exp (I * ⟪t,x⟫)` and its inverse factor `(2π)⁻ᵈ`. The proof specializes
Mathlib's Euclidean Lebesgue Gaussian integral at `b = 1/(2σ²)` and `b = σ²/2`.
There is no nonzero-dimension assumption.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace ProbabilityFoundations.Ch07

/-- The centered isotropic Gaussian density of standard deviation `σ`. -/
noncomputable def gaussianDensity {d : ℕ} (σ : ℝ) (x : Euclidean d) : ℝ :=
  (2 * Real.pi * σ ^ 2) ^ (-(d : ℝ) / 2) *
    Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))

theorem gaussianDensity_nonnegative {d : ℕ} {σ : ℝ} (_hσ : 0 < σ)
    (x : Euclidean d) : 0 ≤ gaussianDensity σ x := by
  unfold gaussianDensity
  positivity

private theorem oscillatory_gaussian {d : ℕ} {b : ℝ} (hb : 0 < b)
    (c : ℂ) (w : Euclidean d) :
    (∫ v : Euclidean d, Complex.exp (- (b : ℂ) * (‖v‖ : ℂ) ^ 2 +
      c * (inner ℝ w v : ℂ))) =
    ((Real.pi / b) ^ ((d : ℝ) / 2) : ℝ) *
      Complex.exp (c ^ 2 * (‖w‖ : ℂ) ^ 2 / (4 * (b : ℂ))) := by
  convert GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (show 0 < (b : ℂ).re from hb) c w using 1
  rw [← Complex.ofReal_div, Complex.ofReal_cpow (by positivity)]
  simp

private theorem gaussian_constant_cancel (d : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    (2 * Real.pi * σ ^ 2) ^ (-(d : ℝ) / 2) *
      (Real.pi / (1 / (2 * σ ^ 2))) ^ ((d : ℝ) / 2) = 1 := by
  have hp : 0 < 2 * Real.pi * σ ^ 2 := by positivity
  have he : Real.pi / (1 / (2 * σ ^ 2)) = 2 * Real.pi * σ ^ 2 := by simp [div_eq_mul_inv]; ring
  rw [he, show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring,
    Real.rpow_neg hp.le, inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hp _))]

private theorem integrable_real_gaussian {d : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Euclidean d => Real.exp (-b * ‖x‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (show 0 < (b : ℂ).re from hb) 0 (0 : Euclidean d)).norm
  simpa [Complex.norm_exp, ← Complex.ofReal_pow] using h

theorem gaussianDensity_integrable {d : ℕ} {σ : ℝ} (hσ : 0 < σ) :
    Integrable (gaussianDensity (d := d) σ) := by
  have h := (integrable_real_gaussian (d := d)
    (show 0 < 1 / (2 * σ ^ 2) by positivity)).const_mul
      ((2 * Real.pi * σ ^ 2) ^ (-(d : ℝ) / 2))
  convert h using 1
  ext x
  unfold gaussianDensity
  congr 2
  ring

theorem integral_gaussianDensity {d : ℕ} {σ : ℝ} (hσ : 0 < σ) :
    ∫ x : Euclidean d, gaussianDensity σ x = 1 := by
  have he (x : Euclidean d) : -‖x‖ ^ 2 / (2 * σ ^ 2) =
      -(1 / (2 * σ ^ 2)) * ‖x‖ ^ 2 := by ring
  simp_rw [gaussianDensity, he]
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
  simpa using gaussian_constant_cancel d hσ

private theorem integral_gaussian_modulation {d : ℕ} {b : ℝ} (hb : 0 < b)
    (c : ℂ) (w : Euclidean d) :
    (∫ v : Euclidean d, Complex.exp (c * (inner ℝ w v : ℂ)) *
      (Real.exp (-b * ‖v‖ ^ 2) : ℂ)) =
    ((Real.pi / b) ^ ((d : ℝ) / 2) : ℝ) *
      Complex.exp (c ^ 2 * (‖w‖ : ℂ) ^ 2 / (4 * (b : ℂ))) := by
  calc
    _ = ∫ v : Euclidean d, Complex.exp (-(b : ℂ) * (‖v‖ : ℂ) ^ 2 +
        c * (inner ℝ w v : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [] with v
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = _ := oscillatory_gaussian hb c w

theorem gaussian_transform {d : ℕ} {σ : ℝ} (hσ : 0 < σ) (t : Euclidean d) :
    (∫ x : Euclidean d, Complex.exp (Complex.I * (inner ℝ t x : ℂ)) *
      (gaussianDensity σ x : ℂ)) =
    Complex.exp (-(σ : ℂ) ^ 2 * (‖t‖ : ℂ) ^ 2 / 2) := by
  have hs : (σ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hσ
  have he (x : Euclidean d) : -‖x‖ ^ 2 / (2 * σ ^ 2) =
      -(1 / (2 * σ ^ 2)) * ‖x‖ ^ 2 := by ring
  simp_rw [gaussianDensity, he, Complex.ofReal_mul,
    mul_left_comm (Complex.exp (Complex.I * (inner ℝ t _ : ℂ)))]
  rw [integral_const_mul, integral_gaussian_modulation (by positivity),
    ← mul_assoc, ← Complex.ofReal_mul, gaussian_constant_cancel d hσ,
    Complex.ofReal_one, one_mul]
  congr 1
  push_cast
  rw [Complex.I_sq]
  field_simp; ring

private theorem gaussian_inverse_constant (d : ℕ) (σ : ℝ) :
    (2 * Real.pi) ^ (-(d : ℝ)) *
      (Real.pi / (σ ^ 2 / 2)) ^ ((d : ℝ) / 2) =
    (2 * Real.pi * σ ^ 2) ^ (-(d : ℝ) / 2) := by
  have he : Real.pi / (σ ^ 2 / 2) = (2 * Real.pi) / σ ^ 2 := by ring
  rw [he, Real.div_rpow (by positivity) (sq_nonneg σ), ← mul_div_assoc,
    ← Real.rpow_add (by positivity),
    show -(d : ℝ) + (d : ℝ) / 2 = -((d : ℝ) / 2) by ring,
    show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring,
    Real.mul_rpow (by positivity) (sq_nonneg σ), Real.rpow_neg (sq_nonneg σ)]
  rfl

theorem gaussian_inverse {d : ℕ} {σ : ℝ} (hσ : 0 < σ) (x : Euclidean d) :
    (gaussianDensity σ x : ℂ) =
    ((2 * Real.pi) ^ (-(d : ℝ)) : ℝ) *
      ∫ t : Euclidean d, Complex.exp (-Complex.I * (inner ℝ t x : ℂ)) *
        Complex.exp (-(σ : ℂ) ^ 2 * (‖t‖ : ℂ) ^ 2 / 2) := by
  have hs : (σ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hσ
  have he (t : Euclidean d) :
      -(σ : ℂ) ^ 2 * (‖t‖ : ℂ) ^ 2 / 2 =
      ((-(σ ^ 2 / 2) * ‖t‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hi (t : Euclidean d) : inner ℝ t x = inner ℝ x t := real_inner_comm x t
  simp_rw [he, ← Complex.ofReal_exp, hi]
  rw [integral_gaussian_modulation (by positivity), ← mul_assoc,
    ← Complex.ofReal_mul, gaussian_inverse_constant d σ]
  unfold gaussianDensity
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  push_cast
  simp only [neg_sq, Complex.I_sq]
  field_simp; ring

end ProbabilityFoundations.Ch07
