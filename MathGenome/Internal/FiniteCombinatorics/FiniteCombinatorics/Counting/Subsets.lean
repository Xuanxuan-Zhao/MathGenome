import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Counting.Subsets

/-!
Subset counts (paper.tex, W04 and W21) and Pascal recurrence (W04).
The library's powerset-cardinality theorem counts all subsets of the given
size, including sizes exceeding the ground-set cardinality.
-/

namespace FiniteCombinatorics.Counting.Subsets

universe u

/-- An n-element set has `Nat.choose n k` subsets of cardinality k. -/
theorem subset_count {α : Type u} (A : Finset α) (n k : ℕ) (hA : A.card = n) :
    (Finset.powersetCard k A).card = Nat.choose n k := by
  rw [Finset.card_powersetCard, hA]

/-- No subset can have more elements than its ground set. -/
theorem subset_count_above {α : Type u} (A : Finset α) (k : ℕ) (h : A.card < k) :
    (Finset.powersetCard k A).card = 0 := by
  rw [Finset.card_powersetCard, Nat.choose_eq_zero_of_lt h]

/-- Pascal recurrence, in the natural-index successor form. -/
theorem pascal (n k : ℕ) :
    Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1) :=
  Nat.choose_succ_succ' n k

/-- The empty subset is the unique zero-element subset. -/
theorem subset_count_zero {α : Type u} (A : Finset α) :
    (Finset.powersetCard 0 A).card = 1 := by
  rw [Finset.card_powersetCard, Nat.choose_zero_right]

/-- The empty ground set, with both the zero and positive-size cases. -/
theorem subset_count_empty {α : Type u} (k : ℕ) :
    (Finset.powersetCard k (∅ : Finset α)).card = if k = 0 then 1 else 0 := by
  cases k <;> simp

end FiniteCombinatorics.Counting.Subsets
