import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.BasesAndNeighborhoods
import Mathlib.Topology.DerivedSet

/-!
Independent full proposition types for paper.tex, d10:01:closure-def,
d10:01:closure-test, and d10:01:closure-laws.
The canonical objects are Mathlib's closure, interior, frontier, Dense,
and derivedSet. Their defining characterizations are explicit obligations
below. Neighborhood and LocalBase are the upstream open-witness predicates.
Every statement allows an empty underlying type and arbitrary topology;
there is no separation axiom. Finite unions include the empty family.
-/

open Set
open scoped Topology
universe u

namespace Specs.D10Topology.Ch01.ClosureCalculus
open _root_.Specs.D10Topology.Ch01.BasesAndNeighborhoods

def closure_eq_closed_intersection : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X),
    closure A = ⋂₀ {F : Set X | IsClosed F ∧ A ⊆ F}

def interior_eq_open_union : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X),
    interior A = ⋃₀ {U : Set X | IsOpen U ∧ U ⊆ A}

def boundary_eq_closure_inter : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X),
    frontier A = closure A ∩ closure Aᶜ

def dense_iff_closure_univ : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X),
    Dense A ↔ closure A = univ

def closure_neighborhood_test : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X) (x : X),
    x ∈ closure A ↔ ∀ N : Set X, Neighborhood t x N → (N ∩ A).Nonempty

def interior_neighborhood_test : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X) (x : X),
    x ∈ interior A ↔ Neighborhood t x A

def closure_localBase_test : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X) (x : X) (L : Set (Set X)) (hL : LocalBase t x L),
    x ∈ closure A ↔ ∀ V ∈ L, (V ∩ A).Nonempty

def interior_localBase_test : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X) (x : X) (L : Set (Set X)) (hL : LocalBase t x L),
    x ∈ interior A ↔ ∃ V ∈ L, V ⊆ A

def derivedSet_eq_neighborhood_test : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X),
    derivedSet A = {x | ∀ N : Set X, Neighborhood t x N → (N ∩ (A \ {x})).Nonempty}

def closure_eq_union_derivedSet : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X),
    closure A = A ∪ derivedSet A

def dense_iff_meets_open : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X),
    Dense A ↔ ∀ U : Set X, IsOpen U → U.Nonempty → (A ∩ U).Nonempty

def closure_extensive : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X),
    A ⊆ closure A

def closure_monotone : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A B : Set X) (hAB : A ⊆ B),
    closure A ⊆ closure B

def closure_idempotent : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X),
    closure (closure A) = closure A

def closure_of_empty : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X],
    closure (∅ : Set X) = ∅

def closure_binary_union : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A B : Set X),
    closure (A ∪ B) = closure A ∪ closure B

def closure_finite_union : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (F : Set (Set X)) (hF : F.Finite),
    closure (⋃₀ F) = ⋃ A ∈ F, closure A

def closed_iff_closure_fixed : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X),
    IsClosed A ↔ closure A = A

def interior_eq_complement_closure : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X),
    interior A = (closure Aᶜ)ᶜ

def boundary_eq_closure_sdiff_interior : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X),
    frontier A = closure A \ interior A

def interior_intersection : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A B : Set X),
    interior (A ∩ B) = interior A ∩ interior B

def boundary_closed : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X),
    IsClosed (frontier A)

def boundary_empty_iff_clopen : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (A : Set X),
    frontier A = ∅ ↔ IsClopen A

end Specs.D10Topology.Ch01.ClosureCalculus
