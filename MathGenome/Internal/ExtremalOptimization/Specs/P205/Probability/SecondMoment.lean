import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.MomentIdentities
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Independent specifications for paper.tex, Theorem p205:W22 and its event-restricted
Cauchy–Schwarz estimate, used in p205:W23. Set integrals equal integrals of
indicators for measurable events (`MeasureTheory.integral_indicator`).
`MemLp X 2 μ` supplies actual finite second moments and integrable first moments.
-/

open MeasureTheory

universe u

namespace Specs.P205.Probability.SecondMoment

/-- Event-restricted Cauchy–Schwarz, with no positive-probability assumption.
The variable may even be signed. -/
def EventCauchySchwarz : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ}, MemLp X 2 μ → ∀ {B : Set Ω}, MeasurableSet B →
      (∫ ω in B, X ω ∂μ) ^ 2 ≤ μ.real B * (∫ ω in B, X ω ^ 2 ∂μ) ∧
      μ.real B * (∫ ω in B, X ω ^ 2 ∂μ) ≤ μ.real B * (∫ ω, X ω ^ 2 ∂μ)

/-- The positive denominator and the second-moment existence bound on an arbitrary
probability space, for a measurable, almost surely nonnegative L² variable. -/
def SecondMomentBound : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ}, Measurable X → MemLp X 2 μ →
      (∀ᵐ ω ∂μ, 0 ≤ X ω) → 0 < (∫ ω, X ω ∂μ) →
      0 < (∫ ω, X ω ^ 2 ∂μ) ∧
      (∫ ω, X ω ∂μ) ^ 2 / (∫ ω, X ω ^ 2 ∂μ) ≤ μ.real {ω | 0 < X ω}

end Specs.P205.Probability.SecondMoment
