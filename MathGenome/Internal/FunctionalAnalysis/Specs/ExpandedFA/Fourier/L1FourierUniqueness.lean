import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.SchwartzFourierConvention
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! Independent specifications for Fourier uniqueness used in the moment,
Hermite and Weyl arguments. All dimensions, including zero, are allowed.
The finite-measure transform uses the same negative 2π phase as the L¹ transform.
Measures are positive as stipulated at paper.tex:16707–16710; the moment
application is to finite positive representing measures. The Gaussian average
parameter is spatial width, so its variance parameter in the source is ε². -/
noncomputable section
open MeasureTheory Filter
open scoped Topology FourierTransform
namespace ExpandedFA.Fourier

def weightedIntegralFourier {d : ℕ} (μ : Measure (Euclidean d))
    (f : Euclidean d → ℂ) (ξ : Euclidean d) : ℂ :=
  ∫ x, Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x ξ : ℝ)) * f x ∂μ

def finiteMeasureFourier {d : ℕ} (μ : Measure (Euclidean d)) (ξ : Euclidean d) : ℂ :=
  weightedIntegralFourier μ (fun _ => 1) ξ

/-- Normalized kernel (πc)^(d/2) exp(-π²c‖x‖²), for c > 0. -/
def gaussianKernel (d : ℕ) (c : ℝ) (x : Euclidean d) : ℂ :=
  (Real.pi * c : ℂ) ^ (d / 2 : ℂ) *
    Complex.exp (-(Real.pi : ℂ) ^ 2 * c * ‖x‖ ^ 2)

def gaussianSmooth {d : ℕ} (c : ℝ) (f : Euclidean d → ℂ) (x : Euclidean d) : ℂ :=
  ∫ y, gaussianKernel d c (x-y) * f y
/-- A fixed positive Gaussian of mass one. -/
def standardGaussian (d : ℕ) (y : Euclidean d) : ℝ :=
  Real.exp (-Real.pi * ‖y‖ ^ 2)

/-- Gaussian averaging with width ε; the convolution formula is specified below. -/
def gaussianAverage {d : ℕ} (ε : ℝ) (f : Euclidean d → ℂ) (x : Euclidean d) : ℂ :=
  ∫ y, standardGaussian d y • f (x - ε • y)
end ExpandedFA.Fourier

namespace Specs.ExpandedFA.Fourier.L1FourierUniqueness
open _root_.ExpandedFA.Fourier

def WeightedUniqueness : Prop := ∀ (d : ℕ) (μ : Measure (Euclidean d)) [SigmaFinite μ]
    (f : Euclidean d → ℂ), Integrable f μ →
    (∀ ξ, weightedIntegralFourier μ f ξ = 0) → f =ᵐ[μ] 0

def L1Uniqueness : Prop := ∀ (d : ℕ) (f : Euclidean d → ℂ), Integrable f →
  (∀ ξ, integralFourier f ξ = 0) → f =ᵐ[volume] 0

def L1Injectivity : Prop := ∀ (d : ℕ) (f g : Euclidean d → ℂ),
  Integrable f → Integrable g →
  (∀ ξ, integralFourier f ξ = integralFourier g ξ) → f =ᵐ[volume] g

def RealL1Uniqueness : Prop := ∀ (d : ℕ) (f : Euclidean d → ℝ), Integrable f →
  (∀ ξ, integralFourier (fun x => (f x : ℂ)) ξ = 0) → f =ᵐ[volume] 0

def AngularUniqueness : Prop := ∀ (d : ℕ) (f : Euclidean d → ℂ), Integrable f →
  (∀ p, angularFourier f p = 0) → f =ᵐ[volume] 0

def ContinuousUniqueness : Prop := ∀ (d : ℕ) (f : Euclidean d → ℂ),
  Integrable f → Continuous f → (∀ ξ, integralFourier f ξ = 0) → ∀ x, f x = 0

def FiniteMeasureUniqueness : Prop := ∀ (d : ℕ) (μ ν : Measure (Euclidean d))
  [IsFiniteMeasure μ] [IsFiniteMeasure ν],
  (∀ ξ, finiteMeasureFourier μ ξ = finiteMeasureFourier ν ξ) → μ = ν

def AngularFiniteMeasureUniqueness : Prop := ∀ (d : ℕ) (μ ν : Measure (Euclidean d))
  [IsFiniteMeasure μ] [IsFiniteMeasure ν],
  (∀ p, (∫ x, Complex.exp (-Complex.I * (inner ℝ x p : ℝ)) ∂μ) =
    ∫ x, Complex.exp (-Complex.I * (inner ℝ x p : ℝ)) ∂ν) → μ = ν

def GaussianVanishing : Prop := ∀ (d : ℕ) (f : Euclidean d → ℂ), Integrable f →
  (∀ ξ, integralFourier f ξ = 0) → ∀ c x, gaussianSmooth c f x = 0

def GaussianContinuousApproximation : Prop := ∀ (d : ℕ) (f : Euclidean d → ℂ),
  Integrable f → ∀ x, ContinuousAt f x →
  Tendsto (fun c => gaussianSmooth c f x) atTop (𝓝 (f x))

def GaussianFourierApproximation : Prop := ∀ (d : ℕ) (f : Euclidean d → ℂ),
  Integrable f → Integrable (integralFourier f) → ∀ x,
  Tendsto (fun c => gaussianSmooth c f x) atTop (𝓝 (𝓕⁻ (integralFourier f) x))
def GaussianMass : Prop := ∀ d, (∀ y, 0 < standardGaussian d y) ∧
  Integrable (standardGaussian d) ∧ (∫ y, standardGaussian d y) = 1

def GaussianAverageConvolution : Prop := ∀ (d : ℕ) (ε : ℝ), 0 < ε →
  ∀ (f : Euclidean d → ℂ) x, gaussianAverage ε f x =
    ∫ y, ((ε ^ d)⁻¹ * standardGaussian d (ε⁻¹ • (x-y))) • f y

def GaussianIntegrability : Prop := ∀ (d : ℕ) (f : Euclidean d → ℂ), Integrable f →
  ∀ ε : ℝ, 0 < ε → Integrable (gaussianAverage ε f)

def GaussianL1Approximation : Prop := ∀ (d : ℕ) (f : Euclidean d → ℂ), Integrable f →
  Tendsto (fun ε => eLpNorm (gaussianAverage ε f - f) 1 volume) (𝓝[>] (0 : ℝ)) (𝓝 0)

end Specs.ExpandedFA.Fourier.L1FourierUniqueness
