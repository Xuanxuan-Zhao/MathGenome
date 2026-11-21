import Mathlib.Order.Antichain
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Finset.Max

/-! Independent statements for the first equality of paper.tex, W55.
Parts are nonempty, pairwise disjoint, and cover the entire finite poset.
The order predicates are Mathlib's ordinary chains and antichains. -/
universe u
noncomputable section
open scoped Classical
namespace Specs.FiniteCombinatorics.Graph.Orders.Dilworth

def IsChainPartitionType := ∀ {P : Type u} [Fintype P] [PartialOrder P],
  Finpartition (Finset.univ : Finset P) → Prop

def IsChainPartitionValue : IsChainPartitionType := fun {P} _ _ p =>
  ∀ c ∈ p.parts, IsChain (· ≤ ·) (c : Set P)

def widthType := ∀ (P : Type u) [Fintype P] [PartialOrder P], ℕ

def widthValue : widthType := by
  classical
  exact fun P _ _ => (Finset.univ.filter
    (fun a : Finset P => IsAntichain (· ≤ ·) (a : Set P))).sup Finset.card

/-- An optimal chain partition and a largest antichain, with their common size
identified as the width. The last clause specifies the minimum chain count. -/
def dilworthType : Prop :=
  ∀ (P : Type u) [Fintype P] [PartialOrder P],
    ∃ (p : Finpartition (Finset.univ : Finset P)) (a : Finset P),
      IsChainPartitionValue p ∧ IsAntichain (· ≤ ·) (a : Set P) ∧
      p.parts.card = a.card ∧ a.card = widthValue P ∧
      (∀ b : Finset P, IsAntichain (· ≤ ·) (b : Set P) → b.card ≤ a.card) ∧
      (∀ q : Finpartition (Finset.univ : Finset P),
        IsChainPartitionValue q → p.parts.card ≤ q.parts.card)

def emptyType : Prop :=
  ∀ (P : Type u) [Fintype P] [PartialOrder P] [IsEmpty P],
    widthValue P = 0 ∧ ∃ p : Finpartition (Finset.univ : Finset P),
      IsChainPartitionValue p ∧ p.parts = ∅

end Specs.FiniteCombinatorics.Graph.Orders.Dilworth
