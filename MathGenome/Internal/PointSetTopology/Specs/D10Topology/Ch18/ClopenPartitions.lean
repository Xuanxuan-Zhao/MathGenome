import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.QuasiComponents
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions

/-! Independent statements for paper.tex, d10:18:clopen-partitions.
A partition is indexed by `Fin n`, has nonempty ambient clopen parts,
is pairwise disjoint, and has the indicated union. Thus `n = 0` is
allowed for an empty space. Diameter is the canonical extended diameter
from Chapter 9, so the strict mesh bound is not a truncated real diameter.
No isolated points means exactly that no singleton is open. -/

open Set
universe u

namespace D10Topology.Ch18.ClopenPartitionsData

def ClopenPartitionOf {X : Type u} [TopologicalSpace X] (A : Set X)
    {n : ℕ} (P : Fin n → Set X) : Prop :=
  (∀ i, IsClopen (P i)) ∧ (∀ i, (P i).Nonempty) ∧
    Pairwise (fun i j => Disjoint (P i) (P j)) ∧ (⋃ i, P i) = A

def Refines {X : Type u} {n m : ℕ} (P : Fin n → Set X) (Q : Fin m → Set X) : Prop :=
  ∀ i, ∃ j, P i ⊆ Q j

end D10Topology.Ch18.ClopenPartitionsData

namespace Specs.D10Topology.Ch18.ClopenPartitions
open _root_.D10Topology.Ch18.ClopenPartitionsData
open _root_.D10Topology.Ch06.QuasiComponentsData
open Specs.D10Topology.Ch09.MetricConventions

def partitionType : Type (u + 1) :=
  {X : Type u} → [TopologicalSpace X] → Set X → {n : ℕ} → (Fin n → Set X) → Prop
def partitionValue : partitionType := @ClopenPartitionOf

def refinesType : Type (u + 1) :=
  {X : Type u} → {n m : ℕ} → (Fin n → Set X) → (Fin m → Set X) → Prop
def refinesValue : refinesType := @Refines

def small_mesh_partition : Prop :=
  ∀ {X : Type u} [d : MetricSpace X] [CompactSpace X], ZeroDimensional X →
    ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (P : Fin n → Set X),
      ClopenPartitionOf univ P ∧ ∀ i, diameter d.toPseudoMetricSpace (P i) < ENNReal.ofReal ε

def small_mesh_refinement : Prop :=
  ∀ {X : Type u} [d : MetricSpace X] [CompactSpace X], ZeroDimensional X →
    ∀ ε : ℝ, 0 < ε → ∀ (m : ℕ) (Q : Fin m → Set X), ClopenPartitionOf univ Q →
      ∃ (n : ℕ) (P : Fin n → Set X), ClopenPartitionOf univ P ∧ Refines P Q ∧
        ∀ i, diameter d.toPseudoMetricSpace (P i) < ENNReal.ofReal ε

def split_clopen_part : Prop :=
  ∀ {X : Type u} [MetricSpace X] [CompactSpace X], ZeroDimensional X →
    (∀ x : X, ¬ IsOpen ({x} : Set X)) →
    ∀ H : Set X, IsClopen H → H.Nonempty → ∀ k : ℕ, 0 < k →
      ∃ P : Fin k → Set X, ClopenPartitionOf H P

end Specs.D10Topology.Ch18.ClopenPartitions
