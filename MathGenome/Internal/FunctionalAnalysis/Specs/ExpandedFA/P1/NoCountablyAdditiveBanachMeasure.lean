import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Set MeasureTheory

namespace Specs.ExpandedFA.P1

/-- A countably additive measure on every subset of the real line cannot both be
translation invariant and extend Lebesgue measure. `⊤` is the power-set sigma
algebra; `NullMeasurableSet` refers to the usual Lebesgue completion. -/
def NoCountablyAdditiveBanachMeasure : Prop :=
  ¬ ∃ μ : @Measure ℝ ⊤,
    (∀ (t : ℝ) (s : Set ℝ), μ ((fun x => x + t) '' s) = μ s) ∧
    (∀ s : Set ℝ, NullMeasurableSet s (volume : Measure ℝ) → μ s = volume s)

end Specs.ExpandedFA.P1
