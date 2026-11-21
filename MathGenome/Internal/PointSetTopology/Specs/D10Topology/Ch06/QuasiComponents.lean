import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.ComponentsAndPaths
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.BasesAndNeighborhoods
import Mathlib.Topology.Connected.TotallyDisconnected

/-! Independent statements for paper.tex, `d10:06:quasicomponent`,
`d10:06:quasicomponent-compact`, and `d10:06:zero-dimensional`.
Zero-dimensionality means existence of a clopen basis, with no separation
axiom. Components and connectedness are the canonical Chapter 6 objects.
All statements allow empty underlying spaces. -/

open Set
universe u

namespace D10Topology.Ch06.QuasiComponentsData

def QuasiComponent {X : Type u} [TopologicalSpace X] (x : X) : Set X :=
  ⋂₀ {H : Set X | IsClopen H ∧ x ∈ H}

def TotallyDisconnected (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ x : X, ComponentsPathsData.Component x = {x}

def ZeroDimensional (X : Type u) [t : TopologicalSpace X] : Prop :=
  ∃ B : Set (Set X), Specs.D10Topology.Ch01.BasesAndNeighborhoods.BasisFor t B ∧
    ∀ H ∈ B, IsClopen H

end D10Topology.Ch06.QuasiComponentsData

namespace Specs.D10Topology.Ch06.QuasiComponents
open _root_.D10Topology.Ch06.QuasiComponentsData
open _root_.D10Topology.Ch06.ComponentsPathsData
open _root_.D10Topology.Ch06.ConnectednessData
open _root_.Specs.D10Topology.Ch01.BasesAndNeighborhoods

def quasiComponentType : Type (u + 1) :=
  {X : Type u} → [TopologicalSpace X] → X → Set X
def quasiComponentValue : quasiComponentType := @QuasiComponent

def spacePredicateType : Type (u + 1) :=
  (X : Type u) → [TopologicalSpace X] → Prop
def totallyDisconnectedValue : spacePredicateType := TotallyDisconnected
def zeroDimensionalValue : spacePredicateType := ZeroDimensional

def mem_quasiComponent : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (x y : X),
    y ∈ QuasiComponent x ↔ ∀ H : Set X, IsClopen H → x ∈ H → y ∈ H

def component_subset_quasiComponent : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (x : X), Component x ⊆ QuasiComponent x

def quasiComponent_eq_component : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X] (x : X),
    QuasiComponent x = Component x

def clopen_component_refinement : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (x : X) (O : Set X), IsOpen O → Component x ⊆ O →
    ∃ H : Set X, IsClopen H ∧ Component x ⊆ H ∧ H ⊆ O

def totallyDisconnected_iff_mathlib : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], TotallyDisconnected X ↔ TotallyDisconnectedSpace X

def zeroDimensional_iff_clopen_basis : Prop :=
  ∀ (X : Type u) [t : TopologicalSpace X],
    ZeroDimensional X ↔ BasisFor t {H : Set X | IsClopen H}

def zeroDimensional_iff_mathlib : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], ZeroDimensional X ↔ ZeroDimensionalSpace X

def compact_t2_totallyDisconnected_iff_zeroDimensional : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X],
    TotallyDisconnected X ↔ ZeroDimensional X

def zeroDimensional_t1_hausdorff : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T1Space X], ZeroDimensional X → T2Space X

def zeroDimensional_t1_totallyDisconnected : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T1Space X],
    ZeroDimensional X → TotallyDisconnected X

/-- Bool represents precisely the source's two points, equipped here with
the explicitly indiscrete topology, not Bool's default discrete topology. -/
def indiscrete_twoPoint_clopen_basis : Prop :=
  letI : TopologicalSpace Bool := ⊤
  BasisFor (⊤ : TopologicalSpace Bool) {(univ : Set Bool)} ∧
    ∀ H ∈ ({(univ : Set Bool)} : Set (Set Bool)), IsClopen H

def indiscrete_twoPoint_connected : Prop :=
  @Connected Bool ⊤

def indiscrete_twoPoint_not_totallyDisconnected : Prop :=
  ¬ @TotallyDisconnected Bool ⊤

end Specs.D10Topology.Ch06.QuasiComponents
