import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.Connectedness
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Products
import Mathlib.Topology.Connected.PathConnected

/-! Independent definitions and full proposition types for paper.tex
`d10:06:components`, `d10:06:component-partition`, and the path image/product
assertions of `d10:06:local-quotients`. The sine-curve counterexample and local
connectedness statements have separate allocated goals.

Connectedness and path connectedness here both allow empty spaces. Paths use
Mathlib's actual closed real unit interval and the subspace topology. A path
in a subset must stay in the subset, not merely join its points in the ambient
space. No separation or nonemptiness hypotheses are implicit. -/

open Set
universe u v

namespace D10Topology.Ch06.ComponentsPathsData

variable {X : Type u} [TopologicalSpace X]

def Component (x : X) : Set X :=
  ⋃₀ {A : Set X | ConnectednessData.ConnectedSubset A ∧ x ∈ A}

abbrev UnitPath (x y : X) := Path x y

def PathConnected (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ x y : X, Nonempty (UnitPath x y)

def PathConnectedSubset (A : Set X) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, JoinedIn A x y

def PathComponent (x : X) : Set X := {y | Nonempty (UnitPath x y)}

/-- The two halves use constant extensions of the original paths, so the
formula is defined at every unit-interval point before continuity is proved. -/
noncomputable def concatenationFunction {x y z : X}
    (p : UnitPath x y) (q : UnitPath y z) (t : unitInterval) : X :=
  if (t : ℝ) ≤ 1 / 2 then p.extend (2 * (t : ℝ))
  else q.extend (2 * (t : ℝ) - 1)

end D10Topology.Ch06.ComponentsPathsData

namespace Specs.D10Topology.Ch06.ComponentsAndPaths
open _root_.D10Topology.Ch06.ComponentsPathsData
open _root_.D10Topology.Ch06.ConnectednessData

def componentType : Type (u + 1) :=
  {X : Type u} → [TopologicalSpace X] → X → Set X
def componentValue : componentType := @Component

def unitPathType : Type (u + 1) :=
  {X : Type u} → [TopologicalSpace X] → X → X → Type u
def unitPathValue : unitPathType := @UnitPath

def pathConnectedType : Type (u + 1) :=
  (X : Type u) → [TopologicalSpace X] → Prop
def pathConnectedValue : pathConnectedType := PathConnected

def pathConnectedSubsetType : Type (u + 1) :=
  {X : Type u} → [TopologicalSpace X] → Set X → Prop
def pathConnectedSubsetValue : pathConnectedSubsetType := @PathConnectedSubset

def pathComponentValue : componentType := @PathComponent

def concatenationFunctionType : Type (u + 1) :=
  {X : Type u} → [TopologicalSpace X] → {x y z : X} →
    UnitPath x y → UnitPath y z → unitInterval → X
noncomputable def concatenationFunctionValue : concatenationFunctionType :=
  @concatenationFunction

def component_eq_mathlib : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (x : X), Component x = connectedComponent x

def component_self : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (x : X), x ∈ Component x

def component_connected : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (x : X), ConnectedSubset (Component x)

def connectedSubset_subset_component : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X) (x : X),
    x ∈ A → ConnectedSubset A → A ⊆ Component x

/-- This gives both directions of the maximal-subset characterization. -/
def component_iff_maximal : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X),
    (∃ x : X, Component x = A) ↔
      A.Nonempty ∧ ConnectedSubset A ∧
        ∀ B : Set X, ConnectedSubset B → A ⊆ B → B ⊆ A

def component_partition : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    (⋃ x : X, Component x) = univ ∧
      ∀ x y : X, Component x = Component y ∨ Disjoint (Component x) (Component y)

def component_closed : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (x : X), IsClosed (Component x)

def unitPath_iff_continuous_endpoints : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (x y : X),
    Nonempty (UnitPath x y) ↔
      ∃ p : unitInterval → X, Continuous p ∧ p 0 = x ∧ p 1 = y

def pathConnected_iff_joined : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], PathConnected X ↔ ∀ x y : X, Joined x y

def pathConnectedSubset_iff_subspace : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X),
    PathConnectedSubset A ↔ PathConnected A

def pathConnectedSubset_iff_empty_or_isPathConnected : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X),
    PathConnectedSubset A ↔ A = ∅ ∨ IsPathConnected A

def concatenation_continuous : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {x y z : X}
    (p : UnitPath x y) (q : UnitPath y z), Continuous (concatenationFunction p q)

def concatenation_endpoints : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {x y z : X}
    (p : UnitPath x y) (q : UnitPath y z),
    concatenationFunction p q 0 = x ∧ concatenationFunction p q 1 = z

def joined_equivalence : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], Equivalence (Joined : X → X → Prop)

def pathComponent_eq_mathlib : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (x : X), PathComponent x = pathComponent x

def pathComponent_self : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (x : X), x ∈ PathComponent x

def pathComponent_pathConnected : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (x : X), PathConnectedSubset (PathComponent x)

def pathConnectedSubset_subset_pathComponent : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X) (x : X),
    x ∈ A → PathConnectedSubset A → A ⊆ PathComponent x

def pathComponent_iff_maximal : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X),
    (∃ x : X, PathComponent x = A) ↔
      A.Nonempty ∧ PathConnectedSubset A ∧
        ∀ B : Set X, PathConnectedSubset B → A ⊆ B → B ⊆ A

def pathComponent_partition : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    (⋃ x : X, PathComponent x) = univ ∧
      ∀ x y : X, PathComponent x = PathComponent y ∨
        Disjoint (PathComponent x) (PathComponent y)

def path_range_connected : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {x y : X} (p : UnitPath x y),
    ConnectedSubset (range p)

def pathConnectedSubset_connected : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X),
    PathConnectedSubset A → ConnectedSubset A

def pathComponent_subset_component : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (x : X), PathComponent x ⊆ Component x

def pathConnectedSubset_image : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (f : X → Y),
    PathConnectedSubset A → ContinuousOn f A → PathConnectedSubset (f '' A)

def pathConnected_range : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y), PathConnected X → Continuous f → PathConnectedSubset (range f)

def pathConnected_surjective_image : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y), PathConnected X → Continuous f → Function.Surjective f → PathConnected Y

/-- Arbitrary index universes, with neither nonempty factors nor a nonempty
index type assumed. The topology is the canonical Chapter 3 product topology. -/
def pathConnected_product : Prop :=
  ∀ {I : Type u} (X : I → Type v) (tX : ∀ i, TopologicalSpace (X i)),
    (∀ i, @PathConnected (X i) (tX i)) →
      @PathConnected (∀ i, X i) (Ch03.Products.productTopologyValue tX)

end Specs.D10Topology.Ch06.ComponentsAndPaths
