import MathGenome.Internal.FourierSobolev.Specs.P102.U3.SchwartzFourier
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! Independent statements for the Gaussian part of paper.tex:1052–1064.
The standard volume and Euclidean model are those of the upstream test space.
All statements quantify over every natural dimension, including zero. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace P102.Specs.U3

def gaussianType : Type := (d : ℕ) → ℝ → Euclidean d → ℝ
def gaussianValue : gaussianType := fun d t x =>
  t ^ (-(d : ℝ) / 2) * Real.exp (-Real.pi * ‖x‖ ^ 2 / t)

def gaussianComplexType : Type := (d : ℕ) → ℝ → Euclidean d → ℂ
def gaussianComplexValue : gaussianComplexType := fun d t x => (gaussianValue d t x : ℂ)

def gaussian_integrable_type : Prop := ∀ (d : ℕ) {t : ℝ}, 0 < t →
  Integrable (gaussianValue d t)

def gaussian_mass_type : Prop := ∀ (d : ℕ) {t : ℝ}, 0 < t →
  (∫ x : Euclidean d, gaussianValue d t x) = 1

def gaussian_fourier_type : Prop := ∀ (d : ℕ) {t : ℝ}, 0 < t → ∀ ξ : Euclidean d,
  (∫ x : Euclidean d,
    Complex.exp ((-2 * Real.pi * inner ℝ x ξ : ℝ) * Complex.I) *
      gaussianComplexValue d t x) = (Real.exp (-Real.pi * t * ‖ξ‖ ^ 2) : ℂ)

def gaussian_check_type : Prop := ∀ (d : ℕ) {t : ℝ}, 0 < t → ∀ ξ : Euclidean d,
  (∫ x : Euclidean d,
    Complex.exp ((2 * Real.pi * inner ℝ x ξ : ℝ) * Complex.I) *
      gaussianComplexValue d t x) = (Real.exp (-Real.pi * t * ‖ξ‖ ^ 2) : ℂ)

def gaussian_schwartz_type : Prop := ∀ (d : ℕ) {t : ℝ}, 0 < t →
  ∃ φ : Test d, (φ : Euclidean d → ℂ) = gaussianComplexValue d t

/-- Absolute integrability of all Fréchet derivatives, with arbitrary polynomial
radial weights; in particular all coordinate derivatives are integrable. -/
def gaussian_derivatives_integrable_type : Prop := ∀ (d : ℕ) {t : ℝ}, 0 < t →
  ∀ k n : ℕ, Integrable (fun x : Euclidean d =>
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (gaussianComplexValue d t) x‖)

def gaussian_coordinate_derivatives_integrable_type : Prop :=
  ∀ (d : ℕ) {t : ℝ}, 0 < t → ∀ (n : ℕ) (β : Fin n → Fin d),
    Integrable (fun x : Euclidean d =>
      iteratedFDeriv ℝ n (gaussianComplexValue d t) x (P102.U3.coordinateVector ∘ β))

end P102.Specs.U3
