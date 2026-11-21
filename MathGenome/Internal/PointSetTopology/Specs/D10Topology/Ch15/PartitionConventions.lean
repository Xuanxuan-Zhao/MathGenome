import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.ClosureSums
import Mathlib.Topology.PartitionOfUnity

/-!
Independent interface for paper.tex, d10:15:partition-definition.
The coefficient maps have codomain the real closed interval [0,1]. Supports
are explicitly the closures of their real nonzero sets, with indexed local
finiteness. The canonical sum is the upstream locally finite pointwise sum.

The definition applies to any family U; in the source it is used for indexed
open covers. No separation, countability, or nonemptiness condition is imposed.
The Mathlib bridge below concerns partitions on the whole space, not merely
on a subset. Its statement retains the actual coefficients at every index.
-/

open Set
universe u v

namespace Specs.D10Topology.Ch15.PartitionConventions

open Specs.D10Topology.Ch15.LocallyFiniteConventions
open Specs.D10Topology.Ch15.ClosureSums

/-- Source partition predicate, using closed supports and interval-valued maps. -/
def SubordinatePartitionOfUnity {X : Type u} {I : Type v} [TopologicalSpace X]
    (U : I → Set X) (φ : I → X → Icc (0 : ℝ) 1) : Prop :=
  (∀ i, Continuous (φ i)) ∧
  (∀ i, closure {x | (φ i x : ℝ) ≠ 0} ⊆ U i) ∧
  LocallyFiniteFamily (fun i => closure {x | (φ i x : ℝ) ≠ 0}) ∧
  ∀ x, pointwiseSum (fun i x => (φ i x : ℝ)) x = 1

def subordinatePartitionType : Type (max u v + 1) :=
  {X : Type u} → {I : Type v} → [TopologicalSpace X] →
    (I → Set X) → (I → X → Icc (0 : ℝ) 1) → Prop

def subordinatePartitionValue : subordinatePartitionType.{u,v} := fun U φ =>
  (∀ i, Continuous (φ i)) ∧
  (∀ i, closure {x | (φ i x : ℝ) ≠ 0} ⊆ U i) ∧
  LocallyFiniteFamily (fun i => closure {x | (φ i x : ℝ) ≠ 0}) ∧
  ∀ x, pointwiseSum (fun i x => (φ i x : ℝ)) x = 1

/-- Exact coefficient-preserving equivalence to Mathlib's real-valued object. -/
def partition_iff_mathlib : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X]
    (U : I → Set X) (φ : I → X → Icc (0 : ℝ) 1),
    SubordinatePartitionOfUnity U φ ↔
      ∃ f : _root_.PartitionOfUnity I X, f.IsSubordinate U ∧
        ∀ i x, f i x = (φ i x : ℝ)

/-- Every library partition has the exact required range and closed supports. -/
def mathlib_partition_properties : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X]
    (f : _root_.PartitionOfUnity I X),
    (∀ i x, f i x ∈ Icc (0 : ℝ) 1) ∧
    (∀ i, tsupport (f i) = closure {x | f i x ≠ 0}) ∧
    LocallyFiniteFamily (fun i => closure {x | f i x ≠ 0}) ∧
    ∀ U : I → Set X,
      f.IsSubordinate U ↔ ∀ i, closure {x | f i x ≠ 0} ⊆ U i

/-- A single finite collection of indices suffices throughout a neighborhood. -/
def partition_locally_sum : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X]
    (U : I → Set X) (φ : I → X → Icc (0 : ℝ) 1),
    SubordinatePartitionOfUnity U φ →
    ∀ x, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ ∃ s : Finset I,
      ∀ y ∈ N, (∀ i, i ∉ s → (φ i y : ℝ) = 0) ∧
        (∑ i ∈ s, (φ i y : ℝ)) = 1

/-- Any finite collection containing all nonzero coefficients gives sum one. -/
def partition_sum_finset : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X]
    (U : I → Set X) (φ : I → X → Icc (0 : ℝ) 1),
    SubordinatePartitionOfUnity U φ →
    ∀ (x : X) (s : Finset I), (∀ i, i ∉ s → (φ i x : ℝ) = 0) →
      (∑ i ∈ s, (φ i x : ℝ)) = 1

/-- Every indexed family on an empty domain is a partition; indices may be empty. -/
def partition_on_empty : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X] [IsEmpty X]
    (U : I → Set X) (φ : I → X → Icc (0 : ℝ) 1),
    SubordinatePartitionOfUnity U φ

/-- Empty indices are possible exactly when the covered space is empty. -/
def partition_empty_index_iff : Prop :=
  ∀ {X : Type u} {I : Type v} [TopologicalSpace X] [IsEmpty I]
    (U : I → Set X) (φ : I → X → Icc (0 : ℝ) 1),
    SubordinatePartitionOfUnity U φ ↔ IsEmpty X

end Specs.D10Topology.Ch15.PartitionConventions
