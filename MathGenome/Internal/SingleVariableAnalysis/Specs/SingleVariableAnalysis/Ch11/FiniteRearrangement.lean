import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Absolute

/-! The finite-target case of K03.11.rearrange_conditional (paper.tex:1097–1106).
The permutation acts on every original index, including indices of zero terms.
Convergence is the ordinary limit of inclusive partial sums, with a finite real target.
-/
namespace Specs.SingleVariableAnalysis.Ch11.FiniteRearrangement

open Absolute PartialSums

def finiteRearrangement : Prop :=
  ∀ a : ℕ → ℝ, realConditionallyConvergesValue a →
    ∀ s : ℝ, ∃ π : Equiv.Perm ℕ,
      realSeriesHasSumValue (fun n => a (π n)) s

end Specs.SingleVariableAnalysis.Ch11.FiniteRearrangement
