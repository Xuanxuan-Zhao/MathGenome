import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.Continuity
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.IntermediateValues
import Mathlib.Topology.Order.IntermediateValue

/-!
# Intermediate values on a real closed interval

K03.03.intermediate_values, paper.tex:547–555. The upstream bridge converts
relative epsilon–delta continuity into `ContinuousOn`. Mathlib's closed and
open intermediate value theorems then apply in either endpoint value order.
No ambient continuity outside [a,b] or differentiability is required.
-/

namespace SingleVariableAnalysis

/-- The closed intermediate value theorem, including reversed values and a = b. -/
theorem intermediate_value_closed (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : RelativeContinuous f (Set.Icc a b)) (v : ℝ)
    (hv : (f a ≤ v ∧ v ≤ f b) ∨ (f b ≤ v ∧ v ≤ f a)) :
    ∃ c ∈ Set.Icc a b, f c = v := by
  have hc : ContinuousOn f (Set.Icc a b) := fun x hx =>
    (relativeContinuousAt_within_iff f (Set.Icc a b) x).mp (hf x hx)
  rcases hv with hv | hv
  · exact intermediate_value_Icc hab hc hv
  · exact intermediate_value_Icc' hab hc hv

/-- Strictly intermediate values have witnesses in the open interval. -/
theorem intermediate_value_open (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : RelativeContinuous f (Set.Icc a b)) (v : ℝ)
    (hv : (f a < v ∧ v < f b) ∨ (f b < v ∧ v < f a)) :
    ∃ c ∈ Set.Ioo a b, f c = v := by
  have hc : ContinuousOn f (Set.Icc a b) := fun x hx =>
    (relativeContinuousAt_within_iff f (Set.Icc a b) x).mp (hf x hx)
  rcases hv with hv | hv
  · exact intermediate_value_Ioo hab.le hc hv
  · exact intermediate_value_Ioo' hab.le hc hv

end SingleVariableAnalysis
