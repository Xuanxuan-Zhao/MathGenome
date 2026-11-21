import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.Continuity

/-!
Independent specification for K03.03.intermediate_values (paper.tex:547–555).
The total function represents its restriction to [a,b]; continuity is tested only
there, including one-sided endpoint continuity. Both endpoint value orders are
allowed. The closed statement includes a = b and the endpoint target values.
-/

namespace Specs.SingleVariableAnalysis.Ch03.IntermediateValues

open Specs.SingleVariableAnalysis.Ch03.Continuity

/-- Every value between the two endpoint values is attained on the closed interval. -/
def intermediateValueClosed : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), a ≤ b →
    relativeContinuousValue f (Set.Icc a b) →
    ∀ v : ℝ, ((f a ≤ v ∧ v ≤ f b) ∨ (f b ≤ v ∧ v ≤ f a)) →
      ∃ c ∈ Set.Icc a b, f c = v

/-- A strictly intermediate value is attained away from both endpoints. -/
def intermediateValueOpen : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), a < b →
    relativeContinuousValue f (Set.Icc a b) →
    ∀ v : ℝ, ((f a < v ∧ v < f b) ∨ (f b < v ∧ v < f a)) →
      ∃ c ∈ Set.Ioo a b, f c = v

end Specs.SingleVariableAnalysis.Ch03.IntermediateValues
