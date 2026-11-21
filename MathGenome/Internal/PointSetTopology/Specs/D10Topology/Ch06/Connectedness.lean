import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Subspaces
import Mathlib.Topology.Connected.Clopen

/-!
Independent source predicates and statements for paper.tex,
`d10:06:connected`, `d10:06:separation-tests`, `d10:06:permanence`.
Connectedness includes the empty space. Subsets carry their canonical
subspace topology. Bool is the source's {0,1}, false = 0 and true = 1;
its topology in the map test is explicitly discrete. Constancy is pairwise
equality, so no attained value is required on an empty domain.
-/

open Set Topology
universe u v w

namespace D10Topology.Ch06.ConnectednessData

def Separation {X : Type u} [TopologicalSpace X] (U V : Set X) : Prop :=
  IsOpen U ∧ IsOpen V ∧ U.Nonempty ∧ V.Nonempty ∧
    U ∪ V = univ ∧ U ∩ V = ∅

def Connected (X : Type u) [TopologicalSpace X] : Prop :=
  ¬ ∃ U V : Set X, Separation U V

def ConnectedSubset {X : Type u} [TopologicalSpace X] (A : Set X) : Prop :=
  Connected A

def Separated {X : Type u} [TopologicalSpace X] (A B : Set X) : Prop :=
  A ∩ closure B = ∅ ∧ B ∩ closure A = ∅

end D10Topology.Ch06.ConnectednessData

namespace Specs.D10Topology.Ch06.Connectedness
open _root_.D10Topology.Ch06.ConnectednessData

def separationType : Type (u + 1) :=
  {X : Type u} → [TopologicalSpace X] → Set X → Set X → Prop
def separationValue : separationType := @Separation

def connectedType : Type (u + 1) := (X : Type u) → [TopologicalSpace X] → Prop
def connectedValue : connectedType := Connected

def connectedSubsetType : Type (u + 1) :=
  {X : Type u} → [TopologicalSpace X] → Set X → Prop
def connectedSubsetValue : connectedSubsetType := @ConnectedSubset

def separatedType : Type (u + 1) :=
  {X : Type u} → [TopologicalSpace X] → Set X → Set X → Prop
def separatedValue : separatedType := @Separated

def connected_iff_preconnectedSpace : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], Connected X ↔ PreconnectedSpace X

def connectedSubset_iff_isPreconnected : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X),
    ConnectedSubset A ↔ IsPreconnected A

def connected_iff_clopen : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    Connected X ↔ ∀ U : Set X, IsClopen U → U = ∅ ∨ U = univ

def connected_iff_bool_maps : Prop :=
  ∀ (X : Type u) [t : TopologicalSpace X],
    Connected X ↔ ∀ f : X → Bool, @Continuous X Bool t ⊥ f → ∀ x y, f x = f y

def connected_of_subsingleton : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [Subsingleton X], Connected X

def connectedSubset_empty : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], ConnectedSubset (∅ : Set X)

def connectedSubset_singleton : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (x : X), ConnectedSubset ({x} : Set X)

def subspace_separation_iff : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (Y A B : Set X), Y = A ∪ B →
    (Separation ((Subtype.val : Y → X) ⁻¹' A) ((Subtype.val : Y → X) ⁻¹' B) ↔
      A.Nonempty ∧ B.Nonempty ∧ Separated A B)

def connectedSubset_image : Prop :=
  ∀ {X : Type u} {Z : Type v} [TopologicalSpace X] [TopologicalSpace Z]
    (A : Set X) (f : X → Z), ConnectedSubset A → ContinuousOn f A →
      ConnectedSubset (f '' A)

def connected_range : Prop :=
  ∀ {X : Type u} {Z : Type v} [TopologicalSpace X] [TopologicalSpace Z]
    (f : X → Z), Connected X → Continuous f → ConnectedSubset (range f)

def connected_surjective_image : Prop :=
  ∀ {X : Type u} {Z : Type v} [TopologicalSpace X] [TopologicalSpace Z]
    (f : X → Z), Connected X → Continuous f → Function.Surjective f → Connected Z

def connectedSubset_between_closure : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A B : Set X),
    ConnectedSubset A → A ⊆ B → B ⊆ closure A → ConnectedSubset B

def connectedSubset_closure : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X),
    ConnectedSubset A → ConnectedSubset (closure A)

def connectedSubset_union_meeting : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {ι : Type v} (C : Set X) (A : ι → Set X),
    C.Nonempty → ConnectedSubset C → (∀ i, ConnectedSubset (A i)) →
      (∀ i, (C ∩ A i).Nonempty) → ConnectedSubset (C ∪ ⋃ i, A i)

def connectedSubset_iUnion_common_point : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {ι : Type v} (A : ι → Set X) (x : X),
    (∀ i, x ∈ A i) → (∀ i, ConnectedSubset (A i)) → ConnectedSubset (⋃ i, A i)

/-- Also covers empty ambient X, for which no common point can be supplied. -/
def connectedSubset_iUnion_empty : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {ι : Type v} [IsEmpty ι] (A : ι → Set X),
    ConnectedSubset (⋃ i, A i)

end Specs.D10Topology.Ch06.Connectedness
