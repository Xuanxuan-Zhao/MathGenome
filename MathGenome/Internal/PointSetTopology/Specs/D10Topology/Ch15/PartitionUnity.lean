import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.PartitionConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.ParacompactNormal

/-!
Independent statements for paper.tex, d10:15:partition (Theorem 15.10).
The partition predicate is the accepted interval-valued predicate with closed
supports subordinate to the original indexed cover. All indices, repeated
members, and empty spaces are retained. Only the forward implication assumes
Hausdorffness. The coverwise refinement statement has arbitrary index universe;
the converse tests indices in the universe of X, as in ParacompactSpace's
equivalent open-cover definition.
-/

open Set
universe u v

namespace Specs.D10Topology.Ch15.PartitionUnity

open Specs.D10Topology.Ch15.PartitionConventions
open Specs.D10Topology.Ch15.LocallyFiniteConventions
open Specs.D10Topology.Ch07.SeparationConventions

def exists_subordinate_partition : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X],
    Paracompact X → t2Value X →
    ∀ U : I → Set X, (∀ i, IsOpen (U i)) → (⋃ i, U i) = univ →
      ∃ φ : I → X → Icc (0 : ℝ) 1, SubordinatePartitionOfUnity U φ

/-- The positive loci give a precise locally finite open refinement, even
without a separation axiom on X or an openness assumption on U. -/
def partition_positive_refinement : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X]
    (U : I → Set X) (φ : I → X → Icc (0 : ℝ) 1),
    SubordinatePartitionOfUnity U φ →
      (∀ i, IsOpen {x | 0 < (φ i x : ℝ)}) ∧
      LocallyFiniteFamily (fun i => {x | 0 < (φ i x : ℝ)}) ∧
      (⋃ i, {x | 0 < (φ i x : ℝ)}) = univ ∧
      ∀ i, {x | 0 < (φ i x : ℝ)} ⊆ U i

def paracompact_of_partitions : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    (∀ (I : Type u) (U : I → Set X),
      (∀ i, IsOpen (U i)) → (⋃ i, U i) = univ →
        ∃ φ : I → X → Icc (0 : ℝ) 1, SubordinatePartitionOfUnity U φ) →
    Paracompact X

end Specs.D10Topology.Ch15.PartitionUnity
