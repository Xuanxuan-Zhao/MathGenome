import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Partition.Foundations
import Mathlib.Algebra.Ring.Parity

/-! Independent specification of W26: the restrictions are imposed on the
shared decreasing-list presentation, and the weight ranges over all naturals. -/
namespace FiniteCombinatorics.Partition.Specs

/-- Partitions whose every part is odd, including the empty partition at zero. -/
def OddPartitions (n : ℕ) :=
  {p : PartitionValue n // ∀ i ∈ p.val, Odd i}

/-- Partitions with no repeated part. -/
def DistinctPartitions (n : ℕ) :=
  {p : PartitionValue n // p.val.Nodup}

/-- Equinumerosity at each weight, with no positivity restriction on the weight. -/
def OddDistinct : Prop :=
  ∀ n : ℕ, Nonempty (OddPartitions n ≃ DistinctPartitions n)

end FiniteCombinatorics.Partition.Specs
