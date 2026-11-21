import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.BochnerGaussian
import Mathlib.MeasureTheory.Measure.Tight

/-! Bochner representation on every real Euclidean space, including dimension zero.
The transform has the manuscript's positive sign and 2π normalization. Measures
are positive by their type; no integrability of the original function is assumed. -/

noncomputable section
open MeasureTheory
open ExpandedFA.Fourier

namespace ExpandedFA.PartIV.BochnerPositive

/-- The Fourier–Stieltjes transform with positive Fourier sign. -/
def transform {d : ℕ} (μ : Measure (Euclidean d)) (x : Euclidean d) : ℂ :=
  ∫ ξ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x ξ : ℝ)) ∂μ

namespace Spec
open PositiveDefiniteContinuity.Spec

def Representation : Prop :=
  ∀ (d : ℕ) (φ : Euclidean d → ℂ), PositiveDefinite φ → ContinuousAt φ 0 →
    ∃! μ : Measure (Euclidean d),
      IsFiniteMeasure μ ∧ Measure.Regular μ ∧
      μ Set.univ = ENNReal.ofReal (φ 0).re ∧ transform μ = φ

def Converse : Prop :=
  ∀ (d : ℕ) (μ : Measure (Euclidean d)), IsFiniteMeasure μ →
    PositiveDefinite (transform μ) ∧ UniformContinuous (transform μ) ∧
      transform μ 0 = (μ.real Set.univ : ℂ)

/-- A cofinal sequence of the source's Gaussian approximants is uniformly tight.
This is the tightness needed to retain full mass and test bounded characters. -/
def GaussianTightness : Prop :=
  ∀ (d : ℕ) (φ : Euclidean d → ℂ), PositiveDefinite φ → ContinuousAt φ 0 →
    IsTightMeasureSet (Set.range (fun n : ℕ =>
      BochnerGaussian.densityMeasure φ ((n + 1 : ℝ)⁻¹)))

end Spec
end ExpandedFA.PartIV.BochnerPositive
