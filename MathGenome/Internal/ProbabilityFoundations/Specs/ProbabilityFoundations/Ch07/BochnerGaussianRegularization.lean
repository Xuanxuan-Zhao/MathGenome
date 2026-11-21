import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.TransformObjects
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Independent statement of the Gaussian regularization stage of
`paper.tex:2649–2680`. Positivity, integrability of the inverse density and
unit mass are conclusions. All natural dimensions, including zero, are allowed. -/

open MeasureTheory
open scoped RealInnerProductSpace

namespace Specs.ProbabilityFoundations.Ch07.BochnerGaussianRegularization
open _root_.ProbabilityFoundations.Ch07
open TransformObjects

def regularizedTransformType := {d : ℕ} → (Euclidean d → ℂ) → ℝ → Euclidean d → ℂ

noncomputable def regularizedTransformValue : regularizedTransformType :=
  fun {_d} φ ε t => φ t * (Real.exp (-ε * ‖t‖ ^ 2 / 2) : ℂ)

def regularizedInverseComplexType := regularizedTransformType

noncomputable def regularizedInverseComplexValue : regularizedInverseComplexType :=
  fun {d} φ ε x => ((2 * Real.pi) ^ (-(d : ℝ)) : ℝ) *
    ∫ t : Euclidean d, Complex.exp (-Complex.I * (inner ℝ t x : ℂ)) *
      regularizedTransformValue φ ε t

def regularizedDensityType := {d : ℕ} → (Euclidean d → ℂ) → ℝ → Euclidean d → ℝ

noncomputable def regularizedDensityValue : regularizedDensityType :=
  fun {_d} φ ε x => (regularizedInverseComplexValue φ ε x).re

def regularizedMeasureType := {d : ℕ} → (Euclidean d → ℂ) → ℝ → Measure (Euclidean d)

noncomputable def regularizedMeasureValue : regularizedMeasureType :=
  fun {_d} φ ε => volume.withDensity (fun x => ENNReal.ofReal (regularizedDensityValue φ ε x))

/-- The inverse integral is a nonnegative, bounded continuous real density of
mass one, and its probability law has exactly the regularized characteristic
function, with the plus-sign probability convention and no frequency rescaling
left in the conclusion. -/
def GaussianRegularization : Prop :=
  ∀ {d : ℕ} (φ : Euclidean d → ℂ), Continuous φ →
    isPositiveDefiniteValue φ → φ 0 = 1 → ∀ (ε : ℝ), 0 < ε →
    Integrable (regularizedTransformValue φ ε) ∧
    isPositiveDefiniteValue (regularizedTransformValue φ ε) ∧
    (∀ x, (regularizedInverseComplexValue φ ε x).im = 0 ∧
      0 ≤ regularizedDensityValue φ ε x) ∧
    Continuous (regularizedInverseComplexValue φ ε) ∧
    (∃ C : ℝ, ∀ x, ‖regularizedInverseComplexValue φ ε x‖ ≤ C) ∧
    Continuous (regularizedDensityValue φ ε) ∧
    Integrable (regularizedDensityValue φ ε) ∧
    (∫ x, regularizedDensityValue φ ε x) = 1 ∧
    IsProbabilityMeasure (regularizedMeasureValue φ ε) ∧
    ∀ t, characteristicFunctionValue (regularizedMeasureValue φ ε) t =
      regularizedTransformValue φ ε t

end Specs.ProbabilityFoundations.Ch07.BochnerGaussianRegularization
