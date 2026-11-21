import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Independent statements for Theorem 5.2 (p205:W21).
Probabilities are the real values of the probability measure, and expectation
is the Bochner integral. A real random variable is explicitly measurable and
integrable. Nonnegative integer values are required only almost everywhere.
-/

open MeasureTheory

namespace Specs.P205.Probability

/-- Markov's inequality, with the inclusive event `a ≤ X`. -/
def MarkovBound : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ), Measurable X → Integrable X μ →
    (∀ᵐ ω ∂μ, 0 ≤ X ω) →
    ∀ a : ℝ, 0 < a → μ.real {ω | a ≤ X ω} ≤ (∫ ω, X ω ∂μ) / a

/-- An integrable random variable with almost-sure nonnegative integer values
and expectation less than one has positive probability of being zero. -/
def ZeroDefectCriterion : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ), Measurable X → Integrable X μ →
    (∀ᵐ ω ∂μ, ∃ n : ℕ, X ω = (n : ℝ)) →
    (∫ ω, X ω ∂μ) < 1 → 0 < μ.real {ω | X ω = 0}

end Specs.P205.Probability
