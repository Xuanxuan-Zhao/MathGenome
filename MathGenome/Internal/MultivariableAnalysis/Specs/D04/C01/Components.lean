import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.EuclideanInterfaces
import Mathlib.Topology.Connected.Basic

/-! Independent statements for chapters/01.tex, d04:01:components.
Connectedness uses `IsPreconnected`, the manuscript's convention that allows
empty connected sets. Components themselves are indexed only by points of U.
The general results apply to any topological space, with no separation axiom. -/
noncomputable section
open Set
universe u
namespace Specs.D04.C01.Components.Model

/-- The source's union of all connected subsets of U containing a. -/
def componentWithin {X : Type u} [TopologicalSpace X] (U : Set X) (a : X) : Set X :=
  ⋃₀ {C : Set X | C ⊆ U ∧ IsPreconnected C ∧ a ∈ C}

/-- A maximal connected subset of U, with maximality in the inclusion order. -/
def IsMaximalConnectedWithin {X : Type u} [TopologicalSpace X]
    (U C : Set X) : Prop :=
  C ⊆ U ∧ IsPreconnected C ∧
    ∀ B : Set X, C ⊆ B → B ⊆ U → IsPreconnected B → B = C

/-- Only components based at actual points of U belong to this family. -/
def componentsWithin {X : Type u} [TopologicalSpace X] (U : Set X) : Set (Set X) :=
  {C | ∃ a ∈ U, componentWithin U a = C}

end Specs.D04.C01.Components.Model

namespace Specs.D04.C01.Components
open Model
open Specs.D04.C01.EuclideanInterfaces.Model

def componentWithinType := {X : Type u} → [TopologicalSpace X] → Set X → X → Set X
def componentWithinValue : componentWithinType := @Model.componentWithin

def IsMaximalConnectedWithinType :=
  {X : Type u} → [TopologicalSpace X] → Set X → Set X → Prop
def IsMaximalConnectedWithinValue : IsMaximalConnectedWithinType :=
  @Model.IsMaximalConnectedWithin

def componentsWithinType := {X : Type u} → [TopologicalSpace X] → Set X → Set (Set X)
def componentsWithinValue : componentsWithinType := @Model.componentsWithin

def componentWithin_eq_standardType : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (U : Set X) (a : X),
    componentWithin U a = connectedComponentIn U a

def componentWithin_subsetType : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (U : Set X) (a : X), componentWithin U a ⊆ U

def mem_componentWithinType : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (U : Set X) (a : X),
    a ∈ U → a ∈ componentWithin U a

def componentWithin_connectedType : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (U : Set X) (a : X),
    IsPreconnected (componentWithin U a)

def subset_componentWithinType : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (U C : Set X) (a : X),
    C ⊆ U → IsPreconnected C → a ∈ C → C ⊆ componentWithin U a

def componentWithin_unique_maximalType : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (U : Set X) (a : X), a ∈ U →
    a ∈ componentWithin U a ∧ IsMaximalConnectedWithin U (componentWithin U a) ∧
      ∀ C : Set X, a ∈ C → IsMaximalConnectedWithin U C → C = componentWithin U a

def componentWithin_eq_of_memType : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (U : Set X) (a b : X),
    b ∈ componentWithin U a → componentWithin U a = componentWithin U b

def componentWithin_eq_of_meetType : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (U : Set X) (a b : X),
    (componentWithin U a ∩ componentWithin U b).Nonempty →
    componentWithin U a = componentWithin U b

/-- Coverage, nonempty blocks, and disjointness of distinct blocks. -/
def componentsWithin_partitionType : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (U : Set X),
    ⋃₀ componentsWithin U = U ∧
      (∀ C ∈ componentsWithin U, C.Nonempty ∧ C ⊆ U ∧ IsPreconnected C) ∧
      ∀ C ∈ componentsWithin U, ∀ D ∈ componentsWithin U, C ≠ D → Disjoint C D

def componentsWithin_unique_memberType : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (U : Set X) (x : X), x ∈ U →
    ∃! C : Set X, C ∈ componentsWithin U ∧ x ∈ C

def componentsWithin_emptyType : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], componentsWithin (∅ : Set X) = ∅

def open_componentWithinType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)), Open U → ∀ a : E n, Open (componentWithin U a)

def componentWithin_polygonallyConnectedType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)), Open U → ∀ a : E n,
    PolygonallyConnected (componentWithin U a)

/-- An explicit specialization to the one-point Euclidean space. -/
def componentWithin_dimension_zeroType : Prop :=
  ∀ (U : Set (E 0)) (a : E 0), a ∈ U → componentWithin U a = U

end Specs.D04.C01.Components
