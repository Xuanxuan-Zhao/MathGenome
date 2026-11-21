import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.PeriodicSetup

/-! K03.19.dirichlet_kernel, paper.tex:4770–4795.
The kernel is the actual finite complex exponential sum, including its values
at multiples of 2π. Integrals are the proper componentwise Darboux integrals.
The removable-limit statement uses the quotient's natural domain, the
complement of 2πℤ. Convolution and transport to arbitrary period origins are
separate allocated obligations. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.DirichletKernel
open Ch08.Integral PeriodicSetup
open scoped BigOperators Topology

abbrev kernelType := ℕ → ℝ → ℂ
def kernelValue : kernelType := fun N t =>
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), modeValue n t

def kernelReal : Prop := ∀ N t, (kernelValue N t).im = 0

def kernelEven : Prop := ∀ N t, kernelValue N (-t) = kernelValue N t

def kernelContinuous : Prop := ∀ N, Continuous (kernelValue N)

def kernelQuotient : Prop := ∀ (N : ℕ) (t : ℝ),
  (∀ k : ℤ, t ≠ (k : ℝ) * (2 * Real.pi)) →
  kernelValue N t = ((Real.sin (((N : ℝ) + 1 / 2) * t) / Real.sin (t / 2) : ℝ) : ℂ)

def kernelAtLattice : Prop := ∀ (N : ℕ) (k : ℤ),
  kernelValue N ((k : ℝ) * (2 * Real.pi)) = ((2 * (N : ℝ) + 1 : ℝ) : ℂ)

def kernelIntegrability : Prop := ∀ N,
  complexIntegrableValue (kernelValue N) (-Real.pi) Real.pi

def kernelIntegralMean : Prop := ∀ (N : ℕ)
  (h : complexIntegrableValue (kernelValue N) (-Real.pi) Real.pi),
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegralValue _ h = 1

def kernelRemovable : Prop := ∀ (N : ℕ) (k : ℤ),
  Filter.Tendsto
    (fun t : ℝ => ((Real.sin (((N : ℝ) + 1 / 2) * t) / Real.sin (t / 2) : ℝ) : ℂ))
    (nhdsWithin ((k : ℝ) * (2 * Real.pi))
      {t : ℝ | ∀ j : ℤ, t ≠ (j : ℝ) * (2 * Real.pi)})
    (nhds ((2 * (N : ℝ) + 1 : ℝ) : ℂ))

end Specs.SingleVariableAnalysis.Ch19.DirichletKernel
