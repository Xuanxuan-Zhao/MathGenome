import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.TransformObjects

/-! Independent statements for paper.tex, equation `eq:gaussian-transform`.
All integrals use Euclidean Lebesgue measure. The natural dimension includes zero. -/
open MeasureTheory
open scoped RealInnerProductSpace

namespace Specs.ProbabilityFoundations.Ch07.GaussianTransform
open _root_.ProbabilityFoundations.Ch07

def gaussianDensityType := {d : ℕ} → ℝ → Euclidean d → ℝ

noncomputable def gaussianDensityValue : gaussianDensityType :=
  fun {d} σ x => (2 * Real.pi * σ ^ 2) ^ (-(d : ℝ) / 2) *
    Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))

def gaussianDensityNonnegative : Prop :=
  ∀ {d : ℕ} {σ : ℝ}, 0 < σ → ∀ x : Euclidean d, 0 ≤ gaussianDensityValue σ x

def gaussianDensityIntegrable : Prop :=
  ∀ {d : ℕ} {σ : ℝ}, 0 < σ → Integrable (gaussianDensityValue (d := d) σ)

def gaussianDensityIntegral : Prop :=
  ∀ {d : ℕ} {σ : ℝ}, 0 < σ → ∫ x : Euclidean d, gaussianDensityValue σ x = 1

def gaussianTransform : Prop :=
  ∀ {d : ℕ} {σ : ℝ}, 0 < σ → ∀ t : Euclidean d,
    (∫ x : Euclidean d, Complex.exp (Complex.I * (inner ℝ t x : ℂ)) *
      (gaussianDensityValue σ x : ℂ)) =
    Complex.exp (-(σ : ℂ) ^ 2 * (‖t‖ : ℂ) ^ 2 / 2)

def gaussianInverse : Prop :=
  ∀ {d : ℕ} {σ : ℝ}, 0 < σ → ∀ x : Euclidean d,
    (gaussianDensityValue σ x : ℂ) =
    ((2 * Real.pi) ^ (-(d : ℝ)) : ℝ) *
      ∫ t : Euclidean d, Complex.exp (-Complex.I * (inner ℝ t x : ℂ)) *
        Complex.exp (-(σ : ℂ) ^ 2 * (‖t‖ : ℂ) ^ 2 / 2)

end Specs.ProbabilityFoundations.Ch07.GaussianTransform
