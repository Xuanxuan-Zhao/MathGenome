import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.SecondMoment

/-!
Independent specification for the strict Paley–Zygmund inequality in
paper.tex, Theorem p205:W23 (first assertion). The hypotheses are precisely
those of the second-moment bound. In particular the threshold is strict,
and the parameter range includes zero.
-/

open MeasureTheory

universe u

namespace Specs.P205.Probability.StrictPaleyZygmund

/-- The strict upper event has the Paley–Zygmund lower bound. -/
def StrictPaleyZygmundBound : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ}, Measurable X → MemLp X 2 μ →
      (∀ᵐ ω ∂μ, 0 ≤ X ω) → 0 < (∫ ω, X ω ∂μ) →
      ∀ {θ : ℝ}, 0 ≤ θ → θ < 1 →
        (1 - θ) ^ 2 * (∫ ω, X ω ∂μ) ^ 2 / (∫ ω, X ω ^ 2 ∂μ) ≤
          μ.real {ω | θ * (∫ x, X x ∂μ) < X ω}

end Specs.P205.Probability.StrictPaleyZygmund
