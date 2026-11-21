import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions

/-!
Independent statements for the subspace and closed-image assertions of
paper.tex, d10:07:heredity-products. Subsets have the canonical induced
topology. Regularity and normality have no separation assumptions built in;
all spaces and subspaces may be empty.
-/

open Set
universe u v

namespace Specs.D10Topology.Ch07.SeparationHeredityImages
open Specs.D10Topology.Ch07.SeparationConventions

def subspace_t0 : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X),
    t0Value X → t0Value A

def subspace_t1 : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X),
    t1Value X → t1Value A

def subspace_t2 : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X),
    t2Value X → t2Value A

def subspace_regular : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X),
    regularValue X → regularValue A

def subspace_completelyRegular : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X),
    completelyRegularValue X → completelyRegularValue A

def subspace_normal_of_closed : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X),
    IsClosed A → normalValue X → normalValue A

def subspace_t3 : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X),
    t3Value X → t3Value A

def subspace_tychonoff : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X),
    tychonoffValue X → tychonoffValue A

def subspace_t4_of_closed : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X),
    IsClosed A → t4Value X → t4Value A

def closed_surjection_normal : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (q : X → Y), Continuous q → IsClosedMap q → Function.Surjective q →
      normalValue X → normalValue Y

def closed_surjection_t1 : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (q : X → Y), IsClosedMap q → Function.Surjective q →
      t1Value X → t1Value Y

def closed_surjection_t4 : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (q : X → Y), Continuous q → IsClosedMap q → Function.Surjective q →
      t4Value X → t4Value Y

end Specs.D10Topology.Ch07.SeparationHeredityImages
