import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Iterations.BracketExistence
import Mathlib.Tactic.NormNum

/-! Root existence in a bracket, including the multiple-root example of p206:W62. -/

namespace NumAnalysis206.Iterations.BracketExistence

/-- The weak sign condition includes all zero-endpoint cases. -/
theorem root_exists_closed (a b : ℝ) (f : ℝ → ℝ) (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (hsign : f a * f b ≤ 0) :
    ∃ p ∈ Set.Icc a b, f p = 0 := by
  rcases mul_nonpos_iff.mp hsign with h | h
  · exact intermediate_value_Icc' hab.le hf ⟨h.2, h.1⟩
  · exact intermediate_value_Icc hab.le hf ⟨h.1, h.2⟩

/-- A negative endpoint product forces the root to be strictly inside the interval. -/
theorem root_exists_open (a b : ℝ) (f : ℝ → ℝ) (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (hsign : f a * f b < 0) :
    ∃ p ∈ Set.Ioo a b, f p = 0 := by
  rcases mul_neg_iff.mp hsign with h | h
  · exact intermediate_value_Ioo' hab.le hf ⟨h.2, h.1⟩
  · exact intermediate_value_Ioo hab.le hf ⟨h.1, h.2⟩

/-- The cubic has three distinct roots in the bracket despite strict endpoint signs. -/
theorem cubic_example : Specs.NumAnalysis206.Iterations.BracketExistence.cubicExample := by
  refine ⟨(continuous_id.mul (continuous_id.pow 2 |>.sub continuous_const)).continuousOn, ?_⟩
  norm_num [Set.mem_Icc]

end NumAnalysis206.Iterations.BracketExistence
