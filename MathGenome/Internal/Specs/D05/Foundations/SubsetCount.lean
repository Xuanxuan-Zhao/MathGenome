import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Defs
import Mathlib.SetTheory.Cardinal.Finite

/-! Independent specifications for paper.tex:352 (subset counting).
All counts and divisions below are in ℕ, independently of any scalar field.
A list over the subtype of a finite set is literally a list of its elements.
-/
namespace D05.Foundations

/-- Ordered lists of length `p` with no repeated entries. -/
def DistinctLists (α : Type*) (p : ℕ) :=
  {l : List α // l.length = p ∧ l.Nodup}

/-- An ordering lists every element exactly once. -/
def Orderings (α : Type*) :=
  {l : List α // l.Nodup ∧ ∀ a : α, a ∈ l}

end D05.Foundations

namespace D05SubsetCountSpec
open D05.Foundations

/-- Every size-`p` subset of an `n`-element set is counted once. -/
def subset_count : Prop :=
  ∀ {α : Type*} (s : Finset α) (n p : ℕ), s.card = n →
    (s.powersetCard p).card = n.choose p

/-- The descending product counts actual distinct lists, in every degree. -/
def ordered_list_count : Prop :=
  ∀ {α : Type*} (s : Finset α) (n p : ℕ), s.card = n →
    Nat.card (DistinctLists s p) = ∏ i ∈ Finset.range p, (n - i)

/-- Every set of size `p`, in particular every size-`p` subset, has `p!` orderings. -/
def orderings_count : Prop :=
  ∀ {α : Type*} (t : Finset α) (p : ℕ), t.card = p →
    Nat.card (Orderings t) = p.factorial

/-- Counting lists by their underlying subset gives a multiplication of counts. -/
def double_count : Prop :=
  ∀ {α : Type*} (s : Finset α) (p : ℕ),
    Nat.card (DistinctLists s p) = p.factorial * (s.powersetCard p).card

/-- Division is by the positive integer `p!`, including `p = 0`. -/
def quotient_formula : Prop :=
  ∀ {α : Type*} (s : Finset α) (n p : ℕ), s.card = n →
    (s.powersetCard p).card = (∏ i ∈ Finset.range p, (n - i)) / p.factorial

/-- Both families are empty when there are too many requested elements. -/
def above_card : Prop :=
  ∀ {α : Type*} (s : Finset α) (n p : ℕ), s.card = n → n < p →
    (s.powersetCard p).card = 0 ∧ Nat.card (DistinctLists s p) = 0

/-- The empty subset and the empty list each contribute one. -/
def degree_zero : Prop :=
  ∀ {α : Type*} (s : Finset α),
    (s.powersetCard 0).card = 1 ∧ Nat.card (DistinctLists s 0) = 1

end D05SubsetCountSpec
