import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.FirstCountableSequences
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.ClosureCalculus
import Mathlib.Topology.Compactness.CountablyCompact

/-! Independent specification for paper.tex d10:05:compact-variants and
 d10:05:countable-compactness. Compactness has no separation axiom.
 Countable covers include finite and empty families; HasFIP includes the empty
 intersection. Accumulation has the punctured-neighborhood meaning. -/

open Set Filter
open scoped Topology
universe u v

namespace Specs.D10Topology.Ch05.CountableCompactness
open Ch05.Compactness Ch04.NetsAndSubnets Ch04.FirstCountableSequences
open Ch01.BasesAndNeighborhoods

/-- The finite subcover property for at most countable families of open sets. -/
def CountableCoverCompact (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ U : Set (Set X), U.Countable → (∀ V ∈ U, IsOpen V) → univ ⊆ ⋃₀ U →
    ∃ V : Set (Set X), V ⊆ U ∧ V.Finite ∧ univ ⊆ ⋃₀ V

/-- Every sequence admits a convergent subsequence with strictly increasing indices. -/
def SequentiallyCompact (X : Type u) [t : TopologicalSpace X] : Prop :=
  ∀ a : ℕ → X, ∃ (x : X) (φ : ℕ → ℕ), StrictMono φ ∧ Converges t (a ∘ φ) x

/-- Every infinite subset has an accumulation point, without assuming T1. -/
def LimitPointCompact (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ A : Set X, A.Infinite → (derivedSet A).Nonempty

def compactnessPropertyType := (X : Type u) → [TopologicalSpace X] → Prop

def countableCoverCompactValue : compactnessPropertyType := CountableCoverCompact

def sequentiallyCompactValue : compactnessPropertyType := SequentiallyCompact

def limitPointCompactValue : compactnessPropertyType := LimitPointCompact

def limitPointCompact_iff_neighborhoods : Prop :=
  ∀ (X : Type u) [t : TopologicalSpace X], LimitPointCompact X ↔
    ∀ A : Set X, A.Infinite → ∃ x : X, ∀ N : Set X,
      Neighborhood t x N → (N ∩ (A \ {x})).Nonempty

def sequence_clusters_iff_mapClusterPt : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (a : ℕ → X) (x : X),
    Clusters t a x ↔ MapClusterPt x atTop a

def countableCoverCompact_iff_isCountablyCompact_univ : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    CountableCoverCompact X ↔ IsCountablyCompact (univ : Set X)

def countableCoverCompact_iff_countablyCompactSpace : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    CountableCoverCompact X ↔ CountablyCompactSpace X

def sequentiallyCompact_iff_isSeqCompact_univ : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    SequentiallyCompact X ↔ IsSeqCompact (univ : Set X)

def sequentiallyCompact_iff_seqCompactSpace : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], SequentiallyCompact X ↔ SeqCompactSpace X

def countableCoverCompact_iff_closed_fip : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], CountableCoverCompact X ↔
    ∀ A : Set (Set X), A.Countable → (∀ F ∈ A, IsClosed F) →
      HasFIP A → (⋂₀ A).Nonempty

def countableCoverCompact_iff_sequence_cluster : Prop :=
  ∀ (X : Type u) [t : TopologicalSpace X],
    CountableCoverCompact X ↔ ∀ a : ℕ → X, ∃ x : X, Clusters t a x

def sequentiallyCompact_implies_countableCoverCompact : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], SequentiallyCompact X → CountableCoverCompact X

/-- No separation assumption is imposed in the first-countable equivalence. -/
def firstCountable_countableCoverCompact_iff_sequentiallyCompact : Prop :=
  ∀ (X : Type u) [t : TopologicalSpace X], FirstCountable t →
    (CountableCoverCompact X ↔ SequentiallyCompact X)

def coverCompact_implies_countableCoverCompact : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], CoverCompact X → CountableCoverCompact X

def countableCoverCompact_implies_limitPointCompact : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], CountableCoverCompact X → LimitPointCompact X

def coverCompact_implies_limitPointCompact : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], CoverCompact X → LimitPointCompact X

/-- Singleton-closedness is retained in the reverse implication. -/
def countableCoverCompact_iff_limitPointCompact : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T1Space X],
    CountableCoverCompact X ↔ LimitPointCompact X

/-- Arbitrary countable index types, including finite and empty ones. -/
def countable_open_cover_finite_subcover : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], CountableCoverCompact X →
    ∀ {ι : Type v} [Countable ι] (U : ι → Set X),
      (∀ i, IsOpen (U i)) → univ ⊆ ⋃ i, U i →
      ∃ s : Finset ι, univ ⊆ ⋃ i ∈ s, U i

def empty_space_countableCoverCompact : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [IsEmpty X], CountableCoverCompact X

def empty_space_sequentiallyCompact : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [IsEmpty X], SequentiallyCompact X

def empty_space_limitPointCompact : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [IsEmpty X], LimitPointCompact X

end Specs.D10Topology.Ch05.CountableCompactness
