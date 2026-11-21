import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyDisk

/-! Independent statements for the Dirichlet-kernel portion of
`paper.tex`, fa2:p4:fourier-failures. The circle has angular period 2π;
its explicitly specified Haar measure has total mass one. -/
noncomputable section
open MeasureTheory Filter
open scoped Real ENNReal Topology

namespace ExpandedFA.PartIV.DirichletKernelSpec

abbrev Circle := HardyDiskSpec.Circle
abbrev L1 := Lp ℂ 1 (AddCircle.haarAddCircle (T := 2 * π))
abbrev haar : Measure Circle := AddCircle.haarAddCircle

/-- Symmetric integer frequencies, including N = 0. -/
def frequencies (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) N

def kernel (N : ℕ) : C(Circle, ℂ) := ∑ n ∈ frequencies N, fourier n

def lebesgueConstant (N : ℕ) : ℝ := ∫ t, ‖kernel N t‖ ∂haar

/-- The actual symmetric Fourier sum, using integral Fourier coefficients. -/
def partialSum (N : ℕ) (f : Circle → ℂ) : C(Circle, ℂ) :=
  ∑ n ∈ frequencies N, fourierCoeff f n • fourier n

/-- Its canonical a.e. class on the original L¹ space. -/
def partialSumL1 (N : ℕ) (f : L1) : L1 :=
  ∑ n ∈ frequencies N, fourierCoeff f n • fourierLp 1 n

/-- Integral convolution with the continuous Dirichlet kernel. -/
def convolution (N : ℕ) (f : Circle → ℂ) (x : Circle) : ℂ :=
  ∫ t, kernel N (x - t) * f t ∂haar

def KernelExponential : Prop := ∀ (N : ℕ) (t : ℝ),
  kernel N (t : Circle) = ∑ n ∈ frequencies N, Complex.exp (Complex.I * n * t)

/-- The removable singularity is treated separately by KernelAtZero. -/
def KernelQuotient : Prop := ∀ (N : ℕ) (t : ℝ), Real.sin (t / 2) ≠ 0 →
  kernel N (t : Circle) =
    ((Real.sin (((N : ℝ) + 1 / 2) * t) / Real.sin (t / 2) : ℝ) : ℂ)

def KernelAtZero : Prop := ∀ N : ℕ, kernel N 0 = (2 * N + 1 : ℂ)
def KernelBound : Prop := ∀ (N : ℕ) (x : Circle), ‖kernel N x‖ ≤ 2 * N + 1

def ConvolutionIdentity : Prop := ∀ (N : ℕ) (f : Circle → ℂ),
  Integrable f haar → ∀ x, partialSum N f x = convolution N f x

def L1Representative : Prop := ∀ (N : ℕ) (f : L1),
  (partialSumL1 N f : Circle → ℂ) =ᵐ[haar] convolution N f

/-- Uniform two-sided bounds, with strictly positive constants and all N ≥ 0. -/
def LogarithmicBounds : Prop := ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
  ∀ N : ℕ, c * Real.log (N + 2) ≤ lebesgueConstant N ∧
    lebesgueConstant N ≤ C * Real.log (N + 2)

def KernelNormDivergence : Prop := Tendsto lebesgueConstant atTop atTop

/-- Existence and the exact norm of the original evaluation functional. -/
def ContinuousEvaluationNorm : Prop := ∀ (N : ℕ) (x : Circle),
  ∃ S : C(Circle, ℂ) →L[ℂ] ℂ,
    (∀ f, S f = partialSum N f x) ∧ ‖S‖ = lebesgueConstant N

/-- A bounded convolution operator on the a.e. quotient, with its exact norm. -/
def L1ConvolutionNorm : Prop := ∀ N : ℕ, ∃ S : L1 →L[ℂ] L1,
  (∀ f, S f = partialSumL1 N f) ∧ ‖S‖ = lebesgueConstant N

/-- Unboundedness of the evaluation operator norms at every prescribed point. -/
def EvaluationUnbounded : Prop := ∀ (x : Circle) (B : ℝ),
  ∃ (N : ℕ) (f : C(Circle, ℂ)), ‖f‖ ≤ 1 ∧ B < ‖partialSum N f x‖

def ConvolutionUnbounded : Prop := ∀ B : ℝ,
  ∃ (N : ℕ) (f : L1), ‖f‖ ≤ 1 ∧ B < ‖partialSumL1 N f‖

/-- Real-valued version, retained under the manuscript's global scalar convention. -/
def realKernel (N : ℕ) : C(Circle, ℝ) :=
  ⟨fun t => (kernel N t).re, by fun_prop⟩
abbrev RealL1 := Lp ℝ 1 (AddCircle.haarAddCircle (T := 2 * π))

def KernelReal : Prop := ∀ (N : ℕ) (x : Circle), (realKernel N x : ℂ) = kernel N x

/-- Integral convolution for real inputs agrees with the same exponential
Fourier sum, and in particular that sum is real. -/
def RealFourierConvolution : Prop := ∀ (N : ℕ) (f : Circle → ℝ),
  Integrable f haar → ∀ x,
    ((∫ t, realKernel N (x - t) * f t ∂haar : ℝ) : ℂ) =
      partialSum N (fun t => (f t : ℂ)) x

def RealContinuousEvaluationNorm : Prop := ∀ (N : ℕ) (x : Circle),
  ∃ S : C(Circle, ℝ) →L[ℝ] ℝ,
    (∀ f, S f = (partialSum N (fun t => (f t : ℂ)) x).re) ∧
      ‖S‖ = lebesgueConstant N

def RealL1ConvolutionNorm : Prop := ∀ N : ℕ, ∃ S : RealL1 →L[ℝ] RealL1,
  (∀ f, (S f : Circle → ℝ) =ᵐ[haar]
    (fun x => ∫ t, realKernel N (x - t) * f t ∂haar)) ∧
      ‖S‖ = lebesgueConstant N

def RealEvaluationUnbounded : Prop := ∀ (x : Circle) (B : ℝ),
  ∃ (N : ℕ) (f : C(Circle, ℝ)), ‖f‖ ≤ 1 ∧
    B < ‖(partialSum N (fun t => (f t : ℂ)) x).re‖

def RealConvolutionUnbounded : Prop := ∀ B : ℝ,
  ∃ (N : ℕ) (S : RealL1 →L[ℝ] RealL1) (f : RealL1),
    (∀ g, (S g : Circle → ℝ) =ᵐ[haar]
      (fun x => ∫ t, realKernel N (x - t) * g t ∂haar)) ∧
    ‖f‖ ≤ 1 ∧ B < ‖S f‖

end ExpandedFA.PartIV.DirichletKernelSpec
