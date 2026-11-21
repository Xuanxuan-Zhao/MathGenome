import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.MeasureDefinitions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Independent specification of `paper.tex`, Corollary
`d13:19:metric-recurrence`. The map is measurable and measure preserving;
no continuity or invertibility is required. The almost-everywhere quantifier
precedes the existence of one increasing sequence of positive return times. -/

namespace Specs.D13Unified.Ch19.MetricRecurrence

universe u
open Filter MeasureTheory
open scoped Topology

/-- Almost every point returns to itself along increasing positive times. -/
def metric_recurrenceStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (T : X → X) (μ : Measure X)
    [IsProbabilityMeasure μ],
    Specs.D13Unified.Ch19.MeasureDefinitions.PreservesMeasure T μ →
    ∀ᵐ x ∂μ, ∃ n : ℕ → ℕ, StrictMono n ∧ (∀ k, 0 < n k) ∧
      Tendsto n atTop atTop ∧
      Tendsto (fun k => T^[n k] x) atTop (𝓝 x)

end Specs.D13Unified.Ch19.MetricRecurrence
