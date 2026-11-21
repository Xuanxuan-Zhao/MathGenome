import MathGenome.Internal.SingleVariableAnalysis.Specs.D03Insertion.FinitePartitionData

/-! Independent statement of existence of the sorted union partition. -/

namespace D03Insertion.Specification

/-- The sorted union has precisely the original nodes, without repetitions,
and is itself a partition of the same interval. -/
def sorted_union_partitionType : Prop :=
  ∀ {a b : ℝ}, a < b → ∀ {s n : ℕ}
    (p : Fin (s + 1) → ℝ) (q : Fin (n + 1) → ℝ),
    D03Insertion.ValidPartition a b p → D03Insertion.ValidPartition a b q →
    ∃ (t : ℕ) (r : Fin (t + 1) → ℝ),
      D03Insertion.ValidPartition a b r ∧
      D03Insertion.nodes r = D03Insertion.nodes p ∪ D03Insertion.nodes q

end D03Insertion.Specification
