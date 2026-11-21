import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-! Independent specification of the real-line clause of
`paper.tex:5354–5377`, `fa2:p1:banach-measure`.

The set function is defined on the full power set, and its values lie in
`ℝ≥0∞`. In particular, agreement includes Lebesgue measurable sets of
infinite measure. `NullMeasurableSet` includes the completion of Borel
Lebesgue measure. No countable additivity is asserted.
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal


namespace Specs.ExpandedFA.P1.BanachRealMeasure

/-- The full real-line extension assertion, with no measurability restriction
on the domain of the constructed finitely additive set function. -/
def banachRealMeasureType : Prop :=
  ∃ m : Set ℝ → ℝ≥0∞,
    m ∅ = 0 ∧
    (∀ s t, Disjoint s t → m (s ∪ t) = m s + m t) ∧
    (∀ (a : ℝ) s, m ((fun x => a + x) '' s) = m s) ∧
    (∀ s, NullMeasurableSet s volume → m s = volume s)

end Specs.ExpandedFA.P1.BanachRealMeasure
