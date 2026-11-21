import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.ElementaryTopologies
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.ProperFilters

/-! Independent propositions for paper.tex, d10:05:cautions.
Compactness means the open-cover property, without a separation axiom.
All subspaces use the induced topology; empty spaces and subsets are allowed.
The two-point space is Bool with precisely the indiscrete topology. -/

open Set Filter
open scoped Topology
universe u

namespace Specs.D10Topology.Ch05.CompactnessExamples
open _root_.Specs.D10Topology.Ch05.Compactness
open _root_.Specs.D10Topology.Ch01.ElementaryTopologies
open _root_.Specs.D10Topology.Ch04.ProperFilters

/-- Every finite topological space is compact, including the empty space. -/
def finite_space_compact : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [Finite X], CoverCompact X

/-- The canonical indiscrete topology is compact on any underlying type. -/
def indiscrete_space_compact : Prop :=
  ∀ (X : Type u), @CoverCompact X ⊤

/-- The singleton open cover of an infinite discrete space has no finite subcover. -/
def discrete_singleton_cover : Prop :=
  ∀ (X : Type u) [Infinite X],
    (∀ U ∈ Set.range (fun x : X => ({x} : Set X)), IsOpen[⊥] U) ∧
    (univ : Set X) ⊆ ⋃₀ Set.range (fun x : X => ({x} : Set X)) ∧
    ∀ V : Set (Set X), V ⊆ Set.range (fun x : X => ({x} : Set X)) →
      V.Finite → ¬ (univ : Set X) ⊆ ⋃₀ V

def infinite_discrete_not_compact : Prop :=
  ∀ (X : Type u) [Infinite X], ¬ @CoverCompact X ⊥

/-- Every subset, with its induced topology, of any cofinite space is compact. -/
def cofinite_subspace_compact : Prop :=
  ∀ (X : Type u) (K : Set X), @SubspaceCompact X (cofiniteTopology X) K

def cofinite_space_compact : Prop :=
  ∀ (X : Type u), @CoverCompact X (cofiniteTopology X)

/-- No existence of an infinite proper subset is silently assumed. -/
def cofinite_infinite_proper_compact_nonclosed : Prop :=
  ∀ (X : Type u) [Infinite X] (A : Set X), A.Infinite → A ≠ univ →
    @SubspaceCompact X (cofiniteTopology X) A ∧ ¬ IsClosed[cofiniteTopology X] A

/-- General indiscrete convergence, stated using the canonical proper-filter interface. -/
def indiscrete_filter_converges : Prop :=
  ∀ (X : Type u) (F : ProperFilter X) (x : X),
    @FilterConverges X ⊤ F.val x

/-- Every proper filter has both distinct points as limits. -/
def two_point_indiscrete_filter_limits : Prop :=
  ∀ F : ProperFilter Bool,
    @FilterConverges Bool ⊤ F.val false ∧ @FilterConverges Bool ⊤ F.val true

end Specs.D10Topology.Ch05.CompactnessExamples
