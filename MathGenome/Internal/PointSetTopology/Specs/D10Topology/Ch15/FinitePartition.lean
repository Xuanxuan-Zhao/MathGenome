import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.PartitionConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions

/-!
Independent specification for paper.tex, d10:15:finite-partition.
The cover and the partition have exactly the same finite index type.
Normality does not include T1, and neither the space nor the indices are
required to be nonempty. Subordination uses closures of nonzero sets,
as fixed in the accepted partition conventions.
-/

open Set
universe u v

namespace Specs.D10Topology.Ch15.FinitePartition

def finite_subordinate_partition : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X] [Finite I],
    Specs.D10Topology.Ch07.SeparationConventions.normalValue X →
    ∀ U : I → Set X, (∀ i, IsOpen (U i)) → (∀ x, ∃ i, x ∈ U i) →
      ∃ φ : I → X → Icc (0 : ℝ) 1,
        PartitionConventions.SubordinatePartitionOfUnity U φ

/-- For empty indices, the cover forces the domain empty and the empty
family is a partition. No separation condition is needed in this case. -/
def empty_index_partition : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X] [IsEmpty I]
    (U : I → Set X), (∀ x, ∃ i, x ∈ U i) →
      IsEmpty X ∧ ∃ φ : I → X → Icc (0 : ℝ) 1,
        PartitionConventions.SubordinatePartitionOfUnity U φ

end Specs.D10Topology.Ch15.FinitePartition
