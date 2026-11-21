import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Partition.EulerProduct
import Mathlib.Algebra.BigOperators.Finprod

noncomputable section
namespace FiniteCombinatorics.Partition.RecurrenceSpecs

/-- The actual partition count, extended by zero to negative integers. -/
def partitionNumberValue (m : ℤ) : ℤ :=
  if 0 ≤ m then (Specs.partitionCountValue m.toNat : ℤ) else 0

def partitionNumberType := ℤ → ℤ

def PartitionNumberNat : Prop :=
  ∀ n : ℕ, partitionNumberValue n = (Specs.partitionCountValue n : ℤ)

def PartitionNumberZero : Prop := partitionNumberValue 0 = 1

def PartitionNumberNegative : Prop :=
  ∀ m : ℤ, m < 0 → partitionNumberValue m = 0

/-- The paired positive and negative pentagonal contributions, for k ≥ 1. -/
def recurrenceTerm (n : ℤ) (k : ℕ+) : ℤ :=
  (-1 : ℤ) ^ ((k : ℕ) + 1) *
    (partitionNumberValue (n - (k : ℤ) * (3 * (k : ℤ) - 1) / 2) +
      partitionNumberValue (n - (k : ℤ) * (3 * (k : ℤ) + 1) / 2))

/-- The displayed sum is an algebraic sum of a finitely supported integer family. -/
def RecurrenceFiniteSupport : Prop :=
  ∀ n : ℤ, (Function.support (recurrenceTerm n)).Finite

/-- Euler's partition recurrence, with the original integer shifts and signs. -/
def PartitionRecurrence : Prop :=
  ∀ n : ℤ, 0 < n →
    partitionNumberValue n = ∑ᶠ k : ℕ+, recurrenceTerm n k

end FiniteCombinatorics.Partition.RecurrenceSpecs
