import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Setoid.Partition

/-! Partitions are represented canonically by sending each element to the least
member of its block. Idempotence makes the fibers nonempty blocks; the inequality
makes their representatives canonical, so no ordering of the blocks is counted.
The implementation establishes equivalence with arbitrary equivalence relations. -/
namespace FiniteCombinatorics.StirlingSecond

@[ext] structure Partition (n : ℕ) where
  rep : Fin n → Fin n
  idempotent : ∀ i, rep (rep i) = rep i
  decreasing : ∀ i, rep i ≤ i

noncomputable instance (n : ℕ) : Fintype (Partition n) :=
  Fintype.ofInjective Partition.rep (fun _ _ h => Partition.ext h)

/-- The nonempty blocks are the fibers indexed by the fixed representatives. -/
def roots {n : ℕ} (p : Partition n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => p.rep i = i)

def WithBlocks (n k : ℕ) := {p : Partition n // (roots p).card = k}

noncomputable instance (n k : ℕ) : Fintype (WithBlocks n k) :=
  inferInstanceAs (Fintype {p : Partition n // (roots p).card = k})

/-- An unordered partition into exactly `k` nonempty blocks. -/
noncomputable def count (n k : ℕ) : ℕ := Fintype.card (WithBlocks n k)

/-- Negative lower indices vanish, without truncated natural subtraction. -/
def secondInt (n : ℕ) (k : ℤ) : ℕ :=
  if 0 ≤ k then Nat.stirlingSecond n k.toNat else 0

end FiniteCombinatorics.StirlingSecond

universe u

namespace Specs.FiniteCombinatorics.StirlingSecond
open _root_.FiniteCombinatorics.StirlingSecond

def countType := ℕ → ℕ → ℕ
noncomputable def countValue : countType := count

def counting : Prop := ∀ n k, count n k = Nat.stirlingSecond n k

def partitionSemantics : Prop := ∀ n, ∃ e : Partition n ≃ Setoid (Fin n),
  ∀ p i j, (e p).r i j ↔ p.rep i = p.rep j

def blockSemantics : Prop := ∀ n (p : Partition n),
  ∃ e : Quotient (Setoid.ker p.rep) ≃ {i // i ∈ roots p},
    ∀ i, (e (Quotient.mk _ i)).val = p.rep i

/-- The count also applies to any finite type, independently of a labeling. -/
def finiteSetCounting : Prop := ∀ (α : Type u) [Fintype α] (k : ℕ),
  Nat.card {P : Setoid.Partitions α // Nat.card P.val = k} =
    Nat.stirlingSecond (Fintype.card α) k

def zeroZero : Prop := count 0 0 = 1

def emptyPositive : Prop := ∀ k, count 0 (k + 1) = 0

def positiveZero : Prop := ∀ n, count (n + 1) 0 = 0

def outOfRange : Prop := ∀ n k, n < k → count n k = 0

def successor : Prop := ∀ n k,
  count (n + 1) (k + 1) = count n k + (k + 1) * count n (k + 1)

def integerBoundary : Prop := ∀ n (k : ℤ), k < 0 → secondInt n k = 0

def integerRecurrence : Prop := ∀ n (k : ℤ),
  secondInt (n + 1) k = secondInt n (k - 1) + k.toNat * secondInt n k

end Specs.FiniteCombinatorics.StirlingSecond
