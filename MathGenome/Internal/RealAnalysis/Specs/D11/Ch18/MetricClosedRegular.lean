import Mathlib.MeasureTheory.Measure.Regular

/-!
Independent statement of paper.tex:5392–5403, `d11:18:metric-closed-regular`.
`BorelSpace` fixes the measurable sets to be exactly the metric Borel sets.
The ball hypothesis is for every positive real radius; balls with nonpositive
radius are empty. The conclusion concerns every Borel set, including sets of
infinite measure. No countability, completeness, or compactness is assumed.
-/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace Specs.D11.Ch18.MetricClosedRegular

def metric_closed_regular : Prop :=
  ∀ {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X),
    (∀ (x : X) (r : ℝ), 0 < r → μ (Metric.ball x r) < ∞) →
    ∀ (E : Set X), MeasurableSet E → ∀ (ε : ℝ), 0 < ε →
      ∃ U F : Set X, IsOpen U ∧ IsClosed F ∧ E ⊆ U ∧ F ⊆ E ∧
        μ (U \ E) < ENNReal.ofReal ε ∧ μ (E \ F) < ENNReal.ofReal ε

end Specs.D11.Ch18.MetricClosedRegular
