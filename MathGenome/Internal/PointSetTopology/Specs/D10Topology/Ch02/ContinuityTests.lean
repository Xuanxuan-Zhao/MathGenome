import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.ClosureCalculus
import Mathlib.Topology.Constructions

/-!
Independent proposition types for paper.tex, d10:02:maps (continuity,
pointwise continuity, open and closed maps), d10:02:continuity-tests and
d10:02:restriction. The canonical map predicates are those of Mathlib;
their paper formulations are explicit obligations below. Subspaces carry
the topology induced by their inclusions. All spaces and subsets may be
empty; no separation axiom is assumed.
-/

open Set
universe u v w

namespace Specs.D10Topology.Ch02.ContinuityTests
open Specs.D10Topology.Ch01.BasesAndNeighborhoods

def continuous_iff_open_preimages : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y),
    Continuous f ↔ ∀ V : Set Y, IsOpen V → IsOpen (f ⁻¹' V)

def continuousAt_iff_neighborhood_preimages : Prop :=
  ∀ {X : Type u} {Y : Type v} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    (f : X → Y) (x : X),
    ContinuousAt f x ↔ ∀ N : Set Y, Neighborhood tY (f x) N →
      Neighborhood tX x (f ⁻¹' N)

def openMap_iff_open_images : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y),
    IsOpenMap f ↔ ∀ U : Set X, IsOpen U → IsOpen (f '' U)

def closedMap_iff_closed_images : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y),
    IsClosedMap f ↔ ∀ F : Set X, IsClosed F → IsClosed (f '' F)

def continuous_iff_pointwise : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y),
    Continuous f ↔ ∀ x : X, ContinuousAt f x

def continuous_iff_neighborhood_preimages : Prop :=
  ∀ {X : Type u} {Y : Type v} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    (f : X → Y),
    Continuous f ↔ ∀ x : X, ∀ N : Set Y, Neighborhood tY (f x) N →
      Neighborhood tX x (f ⁻¹' N)

def continuous_iff_closed_preimages : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y),
    Continuous f ↔ ∀ F : Set Y, IsClosed F → IsClosed (f ⁻¹' F)

def continuous_iff_closure_images : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y),
    Continuous f ↔ ∀ A : Set X, f '' closure A ⊆ closure (f '' A)

/-- A subbasis generates the target topology, without any covering condition. -/
def continuous_iff_subbasis : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [tY : TopologicalSpace Y]
    (f : X → Y) (S : Set (Set Y)), tY = TopologicalSpace.generateFrom S →
    (Continuous f ↔ ∀ V ∈ S, IsOpen (f ⁻¹' V))

def continuous_iff_basis : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [tY : TopologicalSpace Y]
    (f : X → Y) (B : Set (Set Y)), BasisFor tY B →
    (Continuous f ↔ ∀ V ∈ B, IsOpen (f ⁻¹' V))

def identity_continuous : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], Continuous (id : X → X)

def constant_continuous : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (y : Y),
    Continuous (fun _ : X => y)

def compose_continuous : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z), Continuous f → Continuous g → Continuous (g ∘ f)

def restriction_continuous : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (A : Set X), Continuous f → Continuous (fun a : A => f a.val)

def corestriction_continuous_iff : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (B : Set Y) (h : range f ⊆ B),
    Continuous (fun x => (⟨f x, h ⟨x, rfl⟩⟩ : B)) ↔ Continuous f

/-- Both sides are topologies on A: the left one is pulled back through B. -/
def subspace_topology_trans : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A B : Set X) (hAB : A ⊆ B),
    TopologicalSpace.induced (fun a : A => (⟨a.val, hAB a.property⟩ : B))
      (inferInstance : TopologicalSpace B) = (inferInstance : TopologicalSpace A)

end Specs.D10Topology.Ch02.ContinuityTests
