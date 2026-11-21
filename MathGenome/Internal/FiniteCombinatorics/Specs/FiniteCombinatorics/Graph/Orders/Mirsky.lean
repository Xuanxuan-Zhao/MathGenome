import Mathlib.Order.Antichain
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Lattice.Nat

open Finset
open scoped Classical

namespace FiniteCombinatorics.Mirsky

variable (P : Type*) [PartialOrder P] [Fintype P]

/-- The height is the maximum cardinality of a chain, including the empty chain. -/
noncomputable def height : ℕ := by
  classical
  exact ((univ : Finset (Finset P)).filter
    (fun (C : Finset P) => IsChain (· ≤ ·) (C : Set P))).sup Finset.card

/-- The largest cardinality of a chain whose largest element is `x`. -/
noncomputable def terminalLength (x : P) : ℕ := by
  classical
  exact ((univ : Finset (Finset P)).filter
    (fun (C : Finset P) => IsChain (· ≤ ·) (C : Set P) ∧ x ∈ C ∧ ∀ y ∈ C, y ≤ x)).sup Finset.card

/-- Finpartitions already enforce coverage, disjointness and nonempty parts. -/
def IsAntichainPartition (Q : Finpartition (univ : Finset P)) : Prop :=
  ∀ A ∈ Q.parts, IsAntichain (· ≤ ·) (A : Set P)

/-- The least possible number of parts in an antichain decomposition. -/
noncomputable def antichainCount : ℕ :=
  sInf {k | ∃ Q : Finpartition (univ : Finset P), IsAntichainPartition P Q ∧ Q.parts.card = k}

end FiniteCombinatorics.Mirsky

namespace Specs.FiniteCombinatorics.Mirsky

open _root_.FiniteCombinatorics.Mirsky

/-- The terminal lengths are actual attained maxima. -/
def terminalAttained : Prop := ∀ (P : Type*) [PartialOrder P] [Fintype P] (x : P),
  ∃ C : Finset P, IsChain (· ≤ ·) (C : Set P) ∧ x ∈ C ∧
    (∀ y ∈ C, y ≤ x) ∧ C.card = terminalLength P x

def terminalStrictMono : Prop := ∀ (P : Type*) [PartialOrder P] [Fintype P],
  StrictMono (terminalLength P)

/-- Both extrema are attained, and every chain and every antichain partition obey the bounds. -/
def mirsky : Prop := ∀ (P : Type*) [PartialOrder P] [Fintype P],
  (∃ C : Finset P, IsChain (· ≤ ·) (C : Set P) ∧ C.card = height P) ∧
  (∃ Q : Finpartition (univ : Finset P), IsAntichainPartition P Q ∧ Q.parts.card = height P) ∧
  (∀ C : Finset P, IsChain (· ≤ ·) (C : Set P) → C.card ≤ height P) ∧
  (∀ Q : Finpartition (univ : Finset P), IsAntichainPartition P Q → height P ≤ Q.parts.card)

def countEqHeight : Prop := ∀ (P : Type*) [PartialOrder P] [Fintype P],
  antichainCount P = height P

def emptyCase : Prop := ∀ (P : Type*) [PartialOrder P] [Fintype P] [IsEmpty P],
  height P = 0 ∧ antichainCount P = 0 ∧
  ∃ Q : Finpartition (univ : Finset P), Q.parts = ∅ ∧ IsAntichainPartition P Q

end Specs.FiniteCombinatorics.Mirsky
