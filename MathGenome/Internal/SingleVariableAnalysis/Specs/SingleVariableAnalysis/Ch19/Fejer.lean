import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.FejerConcentration

/-! K03.19.fejer, paper.tex:4958–4977. Uniformity is on the entire real
line, for the actual finite Cesaro means of the upstream Darboux Fourier
coefficients. Real scalars use the canonical embedding into ℂ. The density
conclusions use finite exponential sums and finite real sine/cosine sums. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.Fejer
open Ch08.Integral PeriodicSetup FejerKernel
open scoped BigOperators

def periodicRegularity : Prop := ∀ (f : ℝ → ℂ), Continuous f →
  Function.Periodic f (2 * Real.pi) →
  UniformContinuous f ∧ (∃ M > 0, ∀ x, ‖f x‖ ≤ M) ∧
    complexIntegrableValue f (-Real.pi) Real.pi

def complexUniformConvergence : Prop := ∀ (f : ℝ → ℂ), Continuous f →
  Function.Periodic f (2 * Real.pi) → ∀ (h : ∀ n : ℤ,
    complexIntegrableValue (fun y => f y * modeValue (-n) y) (-Real.pi) Real.pi),
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x : ℝ,
    ‖meanValue f h n x - f x‖ < ε

def realUniformConvergence : Prop := ∀ (f : ℝ → ℝ), Continuous f →
  Function.Periodic f (2 * Real.pi) → ∀ (h : ∀ n : ℤ,
    complexIntegrableValue (fun y => (f y : ℂ) * modeValue (-n) y) (-Real.pi) Real.pi),
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x : ℝ,
    ‖meanValue (fun y => (f y : ℂ)) h n x - (f x : ℂ)‖ < ε

def meanPolynomial : Prop := ∀ (f : ℝ → ℂ)
  (h : ∀ n : ℤ, complexIntegrableValue (fun y => f y * modeValue (-n) y)
    (-Real.pi) Real.pi) (N : ℕ), ∃ c : ℤ → ℂ, ∀ x : ℝ,
  meanValue f h N x = ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), c n * modeValue n x

def complexDensity : Prop := ∀ (f : ℝ → ℂ), Continuous f →
  Function.Periodic f (2 * Real.pi) → ∀ ε : ℝ, 0 < ε →
  ∃ (N : ℕ) (c : ℤ → ℂ), ∀ x : ℝ,
    ‖(∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), c n * modeValue n x) - f x‖ < ε

def realDensity : Prop := ∀ (f : ℝ → ℝ), Continuous f →
  Function.Periodic f (2 * Real.pi) → ∀ ε : ℝ, 0 < ε →
  ∃ (N : ℕ) (a b : ℤ → ℝ), ∀ x : ℝ,
    |(∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (a n * Real.cos ((n : ℝ)*x) + b n * Real.sin ((n : ℝ)*x))) - f x| < ε

end Specs.SingleVariableAnalysis.Ch19.Fejer
