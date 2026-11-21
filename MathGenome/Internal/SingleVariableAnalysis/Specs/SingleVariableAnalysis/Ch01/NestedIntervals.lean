import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SequenceLimit
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Set.Lattice.Indexed

/-!
Independent specification of `K03.01.nested_intervals` (paper.tex:252–258).
All endpoints are finite real numbers. `a n ≤ b n` expresses nonemptiness of
`[a n, b n]`; `Set.Icc` supplies exactly the closed bounded interval.
As in the upstream sequence interface, Lean index `n` denotes source index
`n + 1`. The nesting assumption is only between consecutive intervals.
-/

namespace Specs.SingleVariableAnalysis.Ch01.NestedIntervals

/-- Nesting alone guarantees a common point. -/
def nestedIntervalsNonempty : Prop :=
  ∀ (a b : ℕ → ℝ),
    (∀ n, a n ≤ b n) →
    (∀ n, Set.Icc (a (n + 1)) (b (n + 1)) ⊆ Set.Icc (a n) (b n)) →
    (⋂ n, Set.Icc (a n) (b n)).Nonempty

/-- Shrinking lengths give an actual singleton intersection. -/
def nestedIntervalsSingleton : Prop :=
  ∀ (a b : ℕ → ℝ),
    (∀ n, a n ≤ b n) →
    (∀ n, Set.Icc (a (n + 1)) (b (n + 1)) ⊆ Set.Icc (a n) (b n)) →
    SequenceLimit.realSequenceConvergesValue (fun n => b n - a n) 0 →
    ∃ x : ℝ, (⋂ n, Set.Icc (a n) (b n)) = {x}

/-- The constant unit intervals satisfy the hypotheses for existence but have
an entire unit interval as their intersection, which is not a singleton. -/
def constantUnitIntervals : Prop :=
  let I : ℕ → Set ℝ := fun _ => Set.Icc 0 1
  (∀ n, (I n).Nonempty) ∧
  (∀ n, I (n + 1) ⊆ I n) ∧
  (⋂ n, I n) = Set.Icc (0 : ℝ) 1 ∧
  ¬ ∃ x : ℝ, (⋂ n, I n) = {x}

end Specs.SingleVariableAnalysis.Ch01.NestedIntervals
