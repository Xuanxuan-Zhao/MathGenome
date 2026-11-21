import Mathlib.Data.Finset.Powerset

/-!
Independent specifications for the subset-counting assertion of paper.tex,
W04 and W21, and the Pascal assertion of W04. Finite sets are represented by
`Finset`; `Finset.mem_powersetCard` identifies its members precisely with
subsets of the specified cardinality. No finiteness of the ambient type is needed.
-/

namespace Specs.FiniteCombinatorics.Counting.Subsets

universe u

/-- The number of k-subsets of any n-element finite set. -/
def SubsetCount : Prop :=
  ∀ {α : Type u} (A : Finset α) (n k : ℕ), A.card = n →
    (Finset.powersetCard k A).card = Nat.choose n k

/-- The counting assertion includes k larger than the ground-set size. -/
def SubsetCountAbove : Prop :=
  ∀ {α : Type u} (A : Finset α) (k : ℕ), A.card < k →
    (Finset.powersetCard k A).card = 0

/-- Pascal recurrence with natural successor indices; together with the zero
column and vanishing entries above the diagonal this includes the boundaries. -/
def Pascal : Prop :=
  ∀ n k : ℕ, Nat.choose (n + 1) (k + 1) =
    Nat.choose n k + Nat.choose n (k + 1)

/-- Every finite set, including the empty one, has one zero-element subset. -/
def SubsetCountZero : Prop :=
  ∀ {α : Type u} (A : Finset α), (Finset.powersetCard 0 A).card = 1

/-- The empty ground set has one empty subset and no positive-size subsets. -/
def SubsetCountEmpty : Prop :=
  ∀ {α : Type u} (k : ℕ),
    (Finset.powersetCard k (∅ : Finset α)).card = if k = 0 then 1 else 0

end Specs.FiniteCombinatorics.Counting.Subsets
