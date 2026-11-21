import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.Convolution

/-! K03.19.fejer_kernel, paper.tex:4928–4956.
Actual finite Cesaro averages, with the same integer modes, Fourier sums and
proper componentwise Darboux integral as the upstream interfaces. Real functions
use the canonical embedding into ℂ. The concentration estimate is allocated to
FejerConcentration, not assumed here. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.FejerKernel
open Ch08.Integral PeriodicSetup DirichletKernel
open scoped BigOperators

abbrev kernelType := ℕ → ℝ → ℂ
def kernelValue : kernelType := fun N t =>
  ((1 / ((N : ℝ) + 1) : ℝ) : ℂ) * ∑ k ∈ Finset.range (N+1), DirichletKernel.kernelValue k t

abbrev meanType := partialSumType
def meanValue : meanType := fun f h N x =>
  ((1 / ((N : ℝ) + 1) : ℝ) : ℂ) * ∑ k ∈ Finset.range (N+1), partialSumValue f h k x

def kernelNormSquare : Prop := ∀ (N : ℕ) (t : ℝ),
  kernelValue N t =
    ((‖∑ j ∈ Finset.range (N+1), modeValue (j : ℤ) t‖ ^ 2 / ((N : ℝ)+1) : ℝ) : ℂ)

def kernelQuotient : Prop := ∀ (N : ℕ) (t : ℝ),
  (∀ k : ℤ, t ≠ (k : ℝ) * (2 * Real.pi)) →
  kernelValue N t =
    ((Real.sin (((N : ℝ)+1)*t/2)^2 /
      (((N : ℝ)+1) * Real.sin (t/2)^2) : ℝ) : ℂ)

def kernelAtLattice : Prop := ∀ (N : ℕ) (k : ℤ),
  kernelValue N ((k : ℝ) * (2 * Real.pi)) = (((N : ℝ)+1 : ℝ) : ℂ)

def kernelReal : Prop := ∀ N t, (kernelValue N t).im = 0
def kernelNonnegative : Prop := ∀ N t, 0 ≤ (kernelValue N t).re
def kernelContinuous : Prop := ∀ N, Continuous (kernelValue N)
def kernelIntegrability : Prop := ∀ N,
  complexIntegrableValue (kernelValue N) (-Real.pi) Real.pi

def kernelIntegralMean : Prop := ∀ (N : ℕ)
  (h : complexIntegrableValue (kernelValue N) (-Real.pi) Real.pi),
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegralValue _ h = 1

def meanConvolution : Prop := ∀ (f : ℝ → ℂ), periodicComplexValue f →
  ∀ (h : ∀ n : ℤ, complexIntegrableValue (fun y => f y * modeValue (-n) y)
    (-Real.pi) Real.pi) (N : ℕ) (x : ℝ),
  ∃ ht : complexIntegrableValue (fun t => f (x-t) * kernelValue N t) (-Real.pi) Real.pi,
    meanValue f h N x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegralValue _ ht

def realMeanConvolution : Prop := ∀ (f : ℝ → ℝ), periodicRealValue f →
  ∀ (h : ∀ n : ℤ, complexIntegrableValue (fun y => (f y : ℂ) * modeValue (-n) y)
    (-Real.pi) Real.pi) (N : ℕ) (x : ℝ),
  ∃ ht : complexIntegrableValue (fun t => (f (x-t) : ℂ) * kernelValue N t)
      (-Real.pi) Real.pi,
    meanValue (fun y => (f y : ℂ)) h N x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegralValue _ ht

end Specs.SingleVariableAnalysis.Ch19.FejerKernel
