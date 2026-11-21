import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.MeasureDefinitions

/-!
Independent specification of `paper.tex`, Theorem `d13:19:poincare-recurrence`.
The measure is finite, including zero, and need not be a probability measure.
The set of positive return times itself is infinite; time zero is excluded.
No topology, injectivity, invertibility, or completion is assumed.
-/

namespace Specs.D13Unified.Ch19.PoincareRecurrence

universe u
open Set MeasureTheory

/-- Almost every point of a measurable set has infinitely many positive returns. -/
def poincare_recurrenceStatement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X)
    [IsFiniteMeasure μ],
    Specs.D13Unified.Ch19.MeasureDefinitions.PreservesMeasure T μ →
    ∀ E : Set X, MeasurableSet E →
      ∀ᵐ x ∂μ, x ∈ E → Set.Infinite {n : ℕ | 1 ≤ n ∧ T^[n] x ∈ E}

end Specs.D13Unified.Ch19.PoincareRecurrence
