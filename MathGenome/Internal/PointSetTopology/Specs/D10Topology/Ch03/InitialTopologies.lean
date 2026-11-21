import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.TopologicalFoundations

/-!
Independent specification for paper.tex, `d10:03:initial` (Theorem 3.3).
The spaces Yᵢ and their topologies are given explicitly; X is only a type.
There are no nonemptiness, separation, or cardinality restrictions.
Coarseness is stated as inclusion of open families, avoiding any ambiguity
from the reverse order on `TopologicalSpace`.
-/

open Set
open scoped Topology
universe u v w z

namespace Specs.D10Topology.Ch03.InitialTopologies
open _root_.D10Topology.Ch01

def initialSubbasisType : Type (max (u + 1) (v + 1) (w + 1)) :=
  {X : Type u} → {I : Type v} → {Y : I → Type w} →
    (tY : ∀ i, TopologicalSpace (Y i)) → (∀ i, X → Y i) → Set (Set X)

def initialSubbasisValue : initialSubbasisType.{u, v, w} :=
  fun tY f => {U | ∃ i V, IsOpen[tY i] V ∧ U = f i ⁻¹' V}

def initialTopologyType : Type (max (u + 1) (v + 1) (w + 1)) :=
  {X : Type u} → {I : Type v} → {Y : I → Type w} →
    (tY : ∀ i, TopologicalSpace (Y i)) → (∀ i, X → Y i) → TopologicalSpace X

def initialTopologyValue : initialTopologyType.{u, v, w} :=
  fun tY f => TopologicalSpace.generateFrom (initialSubbasisValue tY f)

def initial_generated : Prop :=
  ∀ {X : Type u} {I : Type v} {Y : I → Type w}
    (tY : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i),
    initialTopologyValue tY f =
      TopologicalSpace.generateFrom {U | ∃ i V, IsOpen[tY i] V ∧ U = f i ⁻¹' V}

def initial_maps_continuous : Prop :=
  ∀ {X : Type u} {I : Type v} {Y : I → Type w}
    (tY : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i) (i : I),
    Continuous[initialTopologyValue tY f, tY i] (f i)

def initial_coarsest : Prop :=
  ∀ {X : Type u} {I : Type v} {Y : I → Type w}
    (tY : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (τ : TopologicalSpace X),
    (∀ i, Continuous[τ, tY i] (f i)) →
      openSets (initialTopologyValue tY f) ⊆ openSets τ

def continuous_initial_iff : Prop :=
  ∀ {X : Type u} {I : Type v} {Y : I → Type w} {Z : Type z}
    (tY : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (tZ : TopologicalSpace Z) (g : Z → X),
    Continuous[tZ, initialTopologyValue tY f] g ↔
      ∀ i, Continuous[tZ, tY i] (f i ∘ g)

def initialSubbasis_empty : Prop :=
  ∀ {X : Type u} {I : Type v} {Y : I → Type w} [IsEmpty I]
    (tY : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i),
    initialSubbasisValue tY f = ∅

def initial_empty : Prop :=
  ∀ {X : Type u} {I : Type v} {Y : I → Type w} [IsEmpty I]
    (tY : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i),
    initialTopologyValue tY f = ⊤

def initial_empty_opens : Prop :=
  ∀ {X : Type u} {I : Type v} {Y : I → Type w} [IsEmpty I]
    (tY : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i),
    openSets (initialTopologyValue tY f) = {∅, univ}

def continuous_initial_empty : Prop :=
  ∀ {X : Type u} {I : Type v} {Y : I → Type w} {Z : Type z} [IsEmpty I]
    (tY : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (tZ : TopologicalSpace Z) (g : Z → X),
    Continuous[tZ, initialTopologyValue tY f] g

end Specs.D10Topology.Ch03.InitialTopologies
