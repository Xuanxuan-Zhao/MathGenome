import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.DirichletKernel
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.PeriodicIntegral

/-! K03.19.dirichlet_kernel (paper.tex:4781–4791) and the even form used
at paper.tex:4806–4816. All integrals are proper componentwise Darboux
integrals, including their actual endpoint values. N is a natural number,
x is arbitrary, and no continuity or one-sided limit of f is assumed.
Real functions use the canonical embedding into ℂ, as in PeriodicSetup;
the real specialization below makes this scope explicit. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.Convolution
open Ch08.Integral PeriodicSetup DirichletKernel

/-- Existence of all products needed in the full and half-period formulas. -/
def translatedProductsIntegrable : Prop := ∀ (f : ℝ → ℂ),
  periodicComplexValue f → ∀ (N : ℕ) (x : ℝ),
  complexIntegrableValue (fun y => f y * kernelValue N (x-y)) (-Real.pi) Real.pi ∧
  complexIntegrableValue (fun t => f (x-t) * kernelValue N t) (-Real.pi) Real.pi ∧
  complexIntegrableValue (fun t => (f (x+t) + f (x-t)) * kernelValue N t) 0 Real.pi

/-- Both full-period convolution identities, with existence witnesses. -/
def convolutionIdentities : Prop := ∀ (f : ℝ → ℂ), periodicComplexValue f →
  ∀ (h : ∀ n : ℤ, complexIntegrableValue (fun y => f y * modeValue (-n) y)
    (-Real.pi) Real.pi) (N : ℕ) (x : ℝ),
  ∃ (hy : complexIntegrableValue (fun y => f y * kernelValue N (x-y)) (-Real.pi) Real.pi)
    (ht : complexIntegrableValue (fun t => f (x-t) * kernelValue N t) (-Real.pi) Real.pi),
    partialSumValue f h N x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegralValue _ hy ∧
    partialSumValue f h N x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegralValue _ ht

/-- Evenness combines the two halves without a singular sine quotient. -/
def evenConvolutionIdentity : Prop := ∀ (f : ℝ → ℂ), periodicComplexValue f →
  ∀ (h : ∀ n : ℤ, complexIntegrableValue (fun y => f y * modeValue (-n) y)
    (-Real.pi) Real.pi) (N : ℕ) (x : ℝ),
  ∃ hh : complexIntegrableValue
    (fun t => (f (x+t) + f (x-t)) * kernelValue N t) 0 Real.pi,
    partialSumValue f h N x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegralValue _ hh

/-- Real scalar functions have the same three identities under the canonical
embedding used by the common complex Fourier partial sum. -/
def realConvolutionIdentities : Prop := ∀ (f : ℝ → ℝ), periodicRealValue f →
  ∀ (h : ∀ n : ℤ, complexIntegrableValue (fun y => (f y : ℂ) * modeValue (-n) y)
    (-Real.pi) Real.pi) (N : ℕ) (x : ℝ),
  ∃ (hy : complexIntegrableValue
      (fun y => (f y : ℂ) * kernelValue N (x-y)) (-Real.pi) Real.pi)
    (ht : complexIntegrableValue
      (fun t => (f (x-t) : ℂ) * kernelValue N t) (-Real.pi) Real.pi)
    (hh : complexIntegrableValue
      (fun t => ((f (x+t) : ℂ) + (f (x-t) : ℂ)) * kernelValue N t) 0 Real.pi),
    partialSumValue (fun y => (f y : ℂ)) h N x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegralValue _ hy ∧
    partialSumValue (fun y => (f y : ℂ)) h N x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegralValue _ ht ∧
    partialSumValue (fun y => (f y : ℂ)) h N x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegralValue _ hh

end Specs.SingleVariableAnalysis.Ch19.Convolution
