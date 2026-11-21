import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.PeriodicSetup

/-! K03.19.uniqueness, paper.tex:4979–4993.
Pointwise uniqueness for continuous functions on ℝ of period 2π, using the
upstream integer Fourier coefficients and proper componentwise Darboux integral.
Real functions use their canonical complex embedding. The explicit integral
witnesses impose no extra regularity: continuity supplies them upstream. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.Uniqueness
open Ch08.Integral PeriodicSetup

def complexZero : Prop := ∀ (f : ℝ → ℂ), Continuous f →
  Function.Periodic f (2 * Real.pi) → ∀ (h : ∀ n : ℤ,
    complexIntegrableValue (fun y => f y * modeValue (-n) y) (-Real.pi) Real.pi),
  (∀ n : ℤ, coefficientValue f n (h n) = 0) → ∀ x : ℝ, f x = 0

def complexUnique : Prop := ∀ (f g : ℝ → ℂ), Continuous f → Continuous g →
  Function.Periodic f (2 * Real.pi) → Function.Periodic g (2 * Real.pi) →
  ∀ (hf : ∀ n : ℤ, complexIntegrableValue (fun y => f y * modeValue (-n) y)
      (-Real.pi) Real.pi)
    (hg : ∀ n : ℤ, complexIntegrableValue (fun y => g y * modeValue (-n) y)
      (-Real.pi) Real.pi),
  (∀ n : ℤ, coefficientValue f n (hf n) = coefficientValue g n (hg n)) → f = g

def realZero : Prop := ∀ (f : ℝ → ℝ), Continuous f →
  Function.Periodic f (2 * Real.pi) → ∀ (h : ∀ n : ℤ,
    complexIntegrableValue (fun y => (f y : ℂ) * modeValue (-n) y)
      (-Real.pi) Real.pi),
  (∀ n : ℤ, coefficientValue (fun y => (f y : ℂ)) n (h n) = 0) →
  ∀ x : ℝ, f x = 0

def realUnique : Prop := ∀ (f g : ℝ → ℝ), Continuous f → Continuous g →
  Function.Periodic f (2 * Real.pi) → Function.Periodic g (2 * Real.pi) →
  ∀ (hf : ∀ n : ℤ, complexIntegrableValue (fun y => (f y : ℂ) * modeValue (-n) y)
      (-Real.pi) Real.pi)
    (hg : ∀ n : ℤ, complexIntegrableValue (fun y => (g y : ℂ) * modeValue (-n) y)
      (-Real.pi) Real.pi),
  (∀ n : ℤ, coefficientValue (fun y => (f y : ℂ)) n (hf n) =
    coefficientValue (fun y => (g y : ℂ)) n (hg n)) → f = g

end Specs.SingleVariableAnalysis.Ch19.Uniqueness
