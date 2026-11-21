import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.PNat.Basic

/-! Independent specification of Definition W24 (paper.tex, Chapter 4).
The list order is decreasing. Multiplicities are indexed by strictly positive
natural numbers; no unconstrained zero coordinate is present. -/
namespace FiniteCombinatorics.Partition.Specs

def PartitionType := ℕ → Type

def PartitionValue (n : ℕ) :=
  {l : List ℕ // l.Pairwise (· ≥ ·) ∧ (∀ i ∈ l, 0 < i) ∧ l.sum = n}

def MultiplicitiesValue (n : ℕ) :=
  {m : ℕ+ →₀ ℕ // m.sum (fun i k => (i : ℕ) * k) = n}

def MultisetRepresentation : Prop :=
  ∀ n, ∃ e : PartitionValue n ≃ Nat.Partition n,
    ∀ p, (e p).parts = (p.val : Multiset ℕ)

def MultiplicityRepresentation : Prop :=
  ∀ n, ∃ e : PartitionValue n ≃ MultiplicitiesValue n,
    ∀ p i, (e p).val i = p.val.count (i : ℕ)

def FiniteRepresentations : Prop :=
  ∀ n, Finite (PartitionValue n) ∧ Finite (MultiplicitiesValue n)

def ZeroPartition : Prop :=
  (∃ p : PartitionValue 0, p.val = []) ∧
  (∀ p : PartitionValue 0, p.val = []) ∧
  (∃ m : MultiplicitiesValue 0, m.val = 0) ∧
  (∀ m : MultiplicitiesValue 0, m.val = 0)

end FiniteCombinatorics.Partition.Specs
