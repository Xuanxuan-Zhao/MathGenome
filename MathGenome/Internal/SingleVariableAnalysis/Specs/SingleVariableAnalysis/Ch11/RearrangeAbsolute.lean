import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.Absolute
import Mathlib.Order.Interval.Finset.Nat

/-!
K03.11.rearrange_absolute (paper.tex:1089–1096).
A grouping is described by strictly increasing cut points k, starting at zero.
Block j consists of all indices in [k j, k (j+1)). Strict increase ensures
nonempty finite blocks and k j ≥ j, so the blocks exhaust all natural indices.
The series predicates are the upstream ordinary inclusive partial-sum limits.
Rearrangements are arbitrary bijections of ℕ, with no order restriction.
-/

namespace Specs.SingleVariableAnalysis.Ch11.RearrangeAbsolute

open PartialSums Absolute
open scoped BigOperators

def realSeriesGrouping : Prop :=
  ∀ (a : ℕ → ℝ) (S : ℝ), realSeriesHasSumValue a S →
    ∀ k : ℕ → ℕ, StrictMono k → k 0 = 0 →
      realSeriesHasSumValue (fun j => ∑ n ∈ Finset.Ico (k j) (k (j + 1)), a n) S

def complexSeriesGrouping : Prop :=
  ∀ (a : ℕ → ℂ) (S : ℂ), complexSeriesHasSumValue a S →
    ∀ k : ℕ → ℕ, StrictMono k → k 0 = 0 →
      complexSeriesHasSumValue (fun j => ∑ n ∈ Finset.Ico (k j) (k (j + 1)), a n) S

def realAbsoluteRearrangement : Prop :=
  ∀ (a : ℕ → ℝ) (S : ℝ), realAbsolutelyConvergesValue a →
    realSeriesHasSumValue a S → ∀ π : Equiv.Perm ℕ,
      realAbsolutelyConvergesValue (a ∘ π) ∧ realSeriesHasSumValue (a ∘ π) S

def complexAbsoluteRearrangement : Prop :=
  ∀ (a : ℕ → ℂ) (S : ℂ), complexAbsolutelyConvergesValue a →
    complexSeriesHasSumValue a S → ∀ π : Equiv.Perm ℕ,
      complexAbsolutelyConvergesValue (a ∘ π) ∧ complexSeriesHasSumValue (a ∘ π) S

end Specs.SingleVariableAnalysis.Ch11.RearrangeAbsolute
