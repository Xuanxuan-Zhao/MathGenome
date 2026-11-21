import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Multinomial

/-!
Independent specifications for the ordered-block assertion of paper.tex W04.
An element of `A` is represented by the subtype of the finset `A`. Thus every
block below is a finite subset of the given ground set. Unique membership in a
block expresses exactly covering and pairwise disjointness; blocks may be empty.
The index `Fin r` records their order, even when some of their sizes coincide.
-/

namespace Specs.FiniteCombinatorics.Counting.OrderedBlocks

universe u

/-- Ordered disjoint blocks covering `A`, with the specified cardinalities. -/
def OrderedBlocks {α : Type u} (A : Finset α) {r : ℕ} (k : Fin r → ℕ) :=
  {B : Fin r → Finset A //
    (∀ i, (B i).card = k i) ∧ (∀ a : A, ∃! i, a ∈ B i)}

noncomputable instance {α : Type u} (A : Finset α) {r : ℕ} (k : Fin r → ℕ) :
    Fintype (OrderedBlocks A k) := by
  classical
  unfold OrderedBlocks
  infer_instance

/-- Type and value specifications for the public alias of the canonical objects. -/
def OrderedBlocksType :=
  ∀ {α : Type u} (_A : Finset α) {r : ℕ}, (Fin r → ℕ) → Type u

def OrderedBlocksValue : OrderedBlocksType := @OrderedBlocks

def BlockCard : Prop :=
  ∀ {α : Type u} (A : Finset α) {r : ℕ} (k : Fin r → ℕ)
    (B : OrderedBlocks A k) (i : Fin r), (B.val i).card = k i

def BlockDisjoint : Prop :=
  ∀ {α : Type u} (A : Finset α) {r : ℕ} (k : Fin r → ℕ)
    (B : OrderedBlocks A k) (i j : Fin r), i ≠ j → Disjoint (B.val i) (B.val j)

def BlockCover : Prop :=
  ∀ {α : Type u} (A : Finset α) {r : ℕ} (k : Fin r → ℕ)
    (B : OrderedBlocks A k) (a : A), ∃ i, a ∈ B.val i

/-- A size-zero block is allowed and is the empty set. -/
def BlockZero : Prop :=
  ∀ {α : Type u} (A : Finset α) {r : ℕ} (k : Fin r → ℕ)
    (B : OrderedBlocks A k) (i : Fin r), k i = 0 → B.val i = ∅

def Count : Prop :=
  ∀ {α : Type u} (A : Finset α) (n r : ℕ) (k : Fin r → ℕ),
    A.card = n → (∑ i, k i) = n →
      Fintype.card (OrderedBlocks A k) = n.factorial / ∏ i, (k i).factorial

def FactorialIdentity : Prop :=
  ∀ {α : Type u} (A : Finset α) (n r : ℕ) (k : Fin r → ℕ),
    A.card = n → (∑ i, k i) = n →
      Fintype.card (OrderedBlocks A k) * (∏ i, (k i).factorial) = n.factorial

def MultinomialCount : Prop :=
  ∀ {α : Type u} (A : Finset α) (n r : ℕ) (k : Fin r → ℕ),
    A.card = n → (∑ i, k i) = n →
      Fintype.card (OrderedBlocks A k) = Nat.multinomial Finset.univ k

/-- Empty ground set, including the empty indexed family. -/
def EmptyCount : Prop :=
  ∀ {α : Type u} (r : ℕ),
    Fintype.card (OrderedBlocks (∅ : Finset α) (fun _ : Fin r => 0)) = 1

end Specs.FiniteCombinatorics.Counting.OrderedBlocks
