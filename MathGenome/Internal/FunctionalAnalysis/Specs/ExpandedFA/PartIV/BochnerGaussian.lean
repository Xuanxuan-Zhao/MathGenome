import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.PositiveDefiniteContinuity
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.SchwartzFourierConvention
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Independent statements for the Gaussian regularization stage of
`paper.tex`, fa2:p4:bochner-positive, lines 18653–18674. The Fourier convention is
exp(-2πi⟪x,ξ⟫), and representation uses the positive sign. Dimensions zero and
zero mass are included. These definitions impose no positivity certificates. -/

noncomputable section
open MeasureTheory

namespace ExpandedFA.PartIV.BochnerGaussian
open ExpandedFA.Fourier

/-- The real Gaussian damping factor, for arbitrary real parameter. -/
def gaussianFactor {d : ℕ} (ε : ℝ) (x : Euclidean d) : ℝ :=
  Real.exp (-Real.pi * ε * ‖x‖ ^ 2)

/-- The manuscript's regularization of the original function. -/
def damped {d : ℕ} (φ : Euclidean d → ℂ) (ε : ℝ) (x : Euclidean d) : ℂ :=
  φ x * (gaussianFactor ε x : ℂ)

/-- The ordinary integral transform, not a formal or distributional transform. -/
def density {d : ℕ} (φ : Euclidean d → ℂ) (ε : ℝ) : Euclidean d → ℂ :=
  integralFourier (damped φ ε)

/-- Once nonnegativity is proved, this is exactly the Fourier density measure. -/
def densityMeasure {d : ℕ} (φ : Euclidean d → ℂ) (ε : ℝ) : Measure (Euclidean d) :=
  volume.withDensity (fun ξ => ENNReal.ofReal (density φ ε ξ).re)

namespace Spec
open PositiveDefiniteContinuity.Spec

def DampingContinuous : Prop :=
  ∀ (d : ℕ) (φ : Euclidean d → ℂ), PositiveDefinite φ → ContinuousAt φ 0 →
    ∀ ε : ℝ, Continuous (damped φ ε)

def DampingIntegrable : Prop :=
  ∀ (d : ℕ) (φ : Euclidean d → ℂ), PositiveDefinite φ → ContinuousAt φ 0 →
    ∀ ε : ℝ, 0 < ε → Integrable (damped φ ε)

def DampingPositiveDefinite : Prop :=
  ∀ (d : ℕ) (φ : Euclidean d → ℂ), PositiveDefinite φ → ContinuousAt φ 0 →
    ∀ ε : ℝ, 0 < ε → PositiveDefinite (damped φ ε)

def FourierNonnegative : Prop :=
  ∀ (d : ℕ) (φ : Euclidean d → ℂ), PositiveDefinite φ → ContinuousAt φ 0 →
    ∀ ε : ℝ, 0 < ε → ∀ ξ, (density φ ε ξ).im = 0 ∧ 0 ≤ (density φ ε ξ).re

def FourierMass : Prop :=
  ∀ (d : ℕ) (φ : Euclidean d → ℂ), PositiveDefinite φ → ContinuousAt φ 0 →
    ∀ ε : ℝ, 0 < ε → Integrable (density φ ε) ∧ ∫ ξ, density φ ε ξ = φ 0

/-- The particular positive-density measure is finite and Radon, has the original
mass, and represents the damped function at every point. -/
def Representation : Prop :=
  ∀ (d : ℕ) (φ : Euclidean d → ℂ), PositiveDefinite φ → ContinuousAt φ 0 →
    ∀ ε : ℝ, 0 < ε →
      IsFiniteMeasure (densityMeasure φ ε) ∧ Measure.Regular (densityMeasure φ ε) ∧
      densityMeasure φ ε Set.univ = ENNReal.ofReal (φ 0).re ∧
      ∀ x, damped φ ε x = ∫ ξ,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x ξ : ℝ))
        ∂densityMeasure φ ε

end Spec
end ExpandedFA.PartIV.BochnerGaussian
