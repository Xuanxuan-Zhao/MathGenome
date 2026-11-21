import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.TransformObjects
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Independent specification of the integrable-characteristic-function clause of
`paper.tex`, Theorem 7.3 and equation `eq:cf-inverse-density`. Lebesgue measure is
on the same Euclidean space as the probability law; dimension zero is included. -/
open MeasureTheory
open scoped RealInnerProductSpace

namespace ProbabilityFoundations.Ch07

/-- The everywhere defined complex inverse integral, with the probability
Fourier convention of the manuscript. -/
noncomputable def inverseCharacteristicIntegral {d : ℕ} (μ : Measure (Euclidean d))
    (x : Euclidean d) : ℂ :=
  ((2 * Real.pi) ^ (-(d : ℝ)) : ℝ) *
    ∫ t : Euclidean d, Complex.exp (-Complex.I * (inner ℝ t x : ℂ)) * charFun μ t

/-- Its real value; the theorem proves the imaginary part vanishes everywhere. -/
noncomputable def inverseCharacteristicDensity {d : ℕ} (μ : Measure (Euclidean d))
    (x : Euclidean d) : ℝ := (inverseCharacteristicIntegral μ x).re

end ProbabilityFoundations.Ch07

namespace Specs.ProbabilityFoundations.Ch07.IntegrableCharacteristicDensity
open _root_.ProbabilityFoundations.Ch07

/-- Absolute convergence of each inverse integral. -/
def InverseIntegrable : Prop :=
  ∀ {d : ℕ} (μ : Measure (Euclidean d)), Integrable (charFun μ) →
    ∀ x : Euclidean d, Integrable
      (fun t => Complex.exp (-Complex.I * (inner ℝ t x : ℂ)) * charFun μ t)

def InverseContinuous : Prop :=
  ∀ {d : ℕ} (μ : Measure (Euclidean d)), Integrable (charFun μ) →
    Continuous (inverseCharacteristicIntegral μ)

def InverseBound : Prop :=
  ∀ {d : ℕ} (μ : Measure (Euclidean d)) (x : Euclidean d),
    ‖inverseCharacteristicIntegral μ x‖ ≤
      (2 * Real.pi) ^ (-(d : ℝ)) * ∫ t : Euclidean d, ‖charFun μ t‖

def InverseReal : Prop :=
  ∀ {d : ℕ} (μ : Measure (Euclidean d)),
    ∀ x : Euclidean d, (inverseCharacteristicIntegral μ x).im = 0

/-- All conclusions, with no density or spatial integrability hypothesis. The
measure equality includes every Borel set, not just continuity sets. -/
def DensityTheorem : Prop :=
  ∀ {d : ℕ} (μ : Measure (Euclidean d)) [IsProbabilityMeasure μ],
    Integrable (charFun μ) →
    (∀ x, (inverseCharacteristicIntegral μ x).im = 0) ∧
    (∀ x, 0 ≤ inverseCharacteristicDensity μ x) ∧
    Continuous (inverseCharacteristicDensity μ) ∧
    (∃ C : ℝ, ∀ x, |inverseCharacteristicDensity μ x| ≤ C) ∧
    Integrable (inverseCharacteristicDensity μ) ∧
    (∫ x, inverseCharacteristicDensity μ x) = 1 ∧
    μ = volume.withDensity (fun x => ENNReal.ofReal (inverseCharacteristicDensity μ x)) ∧
    (∀ A : Set (Euclidean d), MeasurableSet A →
      μ A = ENNReal.ofReal (∫ x in A, inverseCharacteristicDensity μ x))

end Specs.ProbabilityFoundations.Ch07.IntegrableCharacteristicDensity
