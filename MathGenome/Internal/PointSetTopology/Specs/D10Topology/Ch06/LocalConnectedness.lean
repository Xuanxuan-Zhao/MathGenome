import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.ComponentsAndPaths
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.QuotientMaps
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.BasesAndNeighborhoods
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.LocallyPathConnected

/-! Independent source definitions and full statements for paper.tex,
`d10:06:local-definitions`, `d10:06:local-characterization`, and the locally
connected quotient-image assertion of `d10:06:local-quotients`.
Neighborhoods are not required to be open. Connectedness and path connectedness
use the accepted source predicates, both allowing empty sets. In the component
characterizations, components are taken in each open subspace and then included
in the ambient space; their openness is ambient openness. -/

open Set Topology
universe u v

namespace D10Topology.Ch06.LocalConnectednessData
open ConnectednessData ComponentsPathsData
open Specs.D10Topology.Ch01.BasesAndNeighborhoods

variable {X : Type u} [t : TopologicalSpace X]

def LocallyConnectedAt (x : X) : Prop :=
  ∀ N : Set X, Neighborhood t x N →
    ∃ V : Set X, Neighborhood t x V ∧ ConnectedSubset V ∧ V ⊆ N

def LocallyPathConnectedAt (x : X) : Prop :=
  ∀ N : Set X, Neighborhood t x N →
    ∃ V : Set X, Neighborhood t x V ∧ PathConnectedSubset V ∧ V ⊆ N

def LocallyConnected (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ x : X, LocallyConnectedAt x

def LocallyPathConnected (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ x : X, LocallyPathConnectedAt x

end D10Topology.Ch06.LocalConnectednessData

namespace Specs.D10Topology.Ch06.LocalConnectedness
open _root_.D10Topology.Ch06.LocalConnectednessData
open _root_.D10Topology.Ch06.ConnectednessData
open _root_.D10Topology.Ch06.ComponentsPathsData
open Specs.D10Topology.Ch01.BasesAndNeighborhoods

def atType : Type (u + 1) := {X : Type u} → [TopologicalSpace X] → X → Prop
def locallyConnectedAtValue : atType := @LocallyConnectedAt
def locallyPathConnectedAtValue : atType := @LocallyPathConnectedAt

def spaceType : Type (u + 1) := (X : Type u) → [TopologicalSpace X] → Prop
def locallyConnectedValue : spaceType := LocallyConnected
def locallyPathConnectedValue : spaceType := LocallyPathConnected

def locallyConnectedAt_iff_nhds : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (x : X),
    LocallyConnectedAt x ↔
      ∀ N ∈ 𝓝 x, ∃ V ∈ 𝓝 x, IsPreconnected V ∧ V ⊆ N

/-- The nonempty library path predicate is justified because a neighborhood
contains x. No nonemptiness hypothesis on X is added. -/
def locallyPathConnectedAt_iff_nhds : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (x : X),
    LocallyPathConnectedAt x ↔
      ∀ N ∈ 𝓝 x, ∃ V ∈ 𝓝 x, IsPathConnected V ∧ V ⊆ N

def locallyConnected_iff_mathlib : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], LocallyConnected X ↔ LocallyConnectedSpace X

def locallyPathConnected_iff_mathlib : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    LocallyPathConnected X ↔ LocallyPathConnectedSpace X

def locallyConnected_iff_open_components : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], LocallyConnected X ↔
    ∀ U : Set X, IsOpen U → ∀ x : U, IsOpen ((Subtype.val : U → X) '' Component x)

def locallyPathConnected_iff_open_pathComponents : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], LocallyPathConnected X ↔
    ∀ U : Set X, IsOpen U → ∀ x : U,
      IsOpen ((Subtype.val : U → X) '' PathComponent x)

def locallyConnected_iff_connected_open_basis : Prop :=
  ∀ (X : Type u) [t : TopologicalSpace X], LocallyConnected X ↔
    BasisFor t {U : Set X | IsOpen U ∧ ConnectedSubset U}

def locallyPathConnected_iff_pathConnected_open_basis : Prop :=
  ∀ (X : Type u) [t : TopologicalSpace X], LocallyPathConnected X ↔
    BasisFor t {U : Set X | IsOpen U ∧ PathConnectedSubset U}

def component_eq_pathComponent_of_locallyPathConnected : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], LocallyPathConnected X →
    ∀ x : X, Component x = PathComponent x

def locallyPathConnected_implies_locallyConnected : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], LocallyPathConnected X → LocallyConnected X

def locallyConnected_open_subspace : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], LocallyConnected X →
    ∀ U : Set X, IsOpen U → LocallyConnected U

def locallyPathConnected_open_subspace : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], LocallyPathConnected X →
    ∀ U : Set X, IsOpen U → LocallyPathConnected U

def locallyConnected_quotient_image : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (q : X → Y), _root_.D10Topology.Ch03.QuotientData.QuotientMap q →
      LocallyConnected X → LocallyConnected Y

end Specs.D10Topology.Ch06.LocalConnectedness
