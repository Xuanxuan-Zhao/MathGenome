import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! Independent specifications for the stars-and-bars paragraph, paper.tex:352.
The objects counted are actual functions `Fin n → ℕ` whose coordinate sum is `p`.
All cardinalities and binomial coefficients are natural numbers.
-/
namespace D05.Foundations

/-- Nonnegative integer `n`-tuples with coordinate sum `p`, including empty tuples. -/
def NonnegativeTuples (n p : ℕ) :=
  {a : Fin n → ℕ // ∑ i, a i = p}

end D05.Foundations

namespace D05StarsBarsSpec
open D05.Foundations

/-- Stars and bars for every positive number of variables and every total. -/
def stars_bars : Prop :=
  ∀ (n p : ℕ), 1 ≤ n →
    Nat.card (NonnegativeTuples n p) = (n + p - 1).choose p

/-- There is one empty tuple of total zero. -/
def zero_variables_zero : Prop :=
  Nat.card (NonnegativeTuples 0 0) = 1

/-- No empty tuple has positive total. -/
def zero_variables_pos : Prop :=
  ∀ (p : ℕ), 0 < p → Nat.card (NonnegativeTuples 0 p) = 0

end D05StarsBarsSpec
