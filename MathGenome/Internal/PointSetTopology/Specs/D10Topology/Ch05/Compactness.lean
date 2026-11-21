import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Subspaces
import Mathlib.Topology.Compactness.Compact

/-!
Independent statements for paper.tex d10:05:compact, d10:05:fip,
and d10:05:compact-heredity. Families are sets of subsets; repeated indices
make no difference to these cover and FIP properties. Empty types and empty
finite families are permitted throughout. Compactness has no Hausdorff axiom.
The subtype in SubspaceCompact carries the canonical induced topology.
-/

open Set
universe u v

namespace Specs.D10Topology.Ch05.Compactness

/-- Every ambient open cover has a finite subcover; the finite family may be empty. -/
def AmbientCoverCompact {X : Type u} [TopologicalSpace X] (K : Set X) : Prop :=
  ∀ U : Set (Set X), (∀ V ∈ U, IsOpen V) → K ⊆ ⋃₀ U →
    ∃ V : Set (Set X), V ⊆ U ∧ V.Finite ∧ K ⊆ ⋃₀ V

/-- Compactness is the open-cover property, without separation assumptions. -/
def CoverCompact (X : Type u) [TopologicalSpace X] : Prop :=
  AmbientCoverCompact (univ : Set X)

/-- The empty finite subfamily is included; its intersection is the whole type. -/
def HasFIP {X : Type u} (A : Set (Set X)) : Prop :=
  ∀ B : Set (Set X), B ⊆ A → B.Finite → (⋂₀ B).Nonempty

/-- A subset is compact in its canonical induced subspace topology. -/
def SubspaceCompact {X : Type u} [TopologicalSpace X] (K : Set X) : Prop :=
  CoverCompact K

-- Definition bindings include both their type and their intended value.
def ambientCoverCompactType : Type (u + 1) :=
  {X : Type u} → [TopologicalSpace X] → Set X → Prop
def ambientCoverCompactValue : ambientCoverCompactType := @AmbientCoverCompact

def coverCompactType : Type (u + 1) :=
  (X : Type u) → [TopologicalSpace X] → Prop
def coverCompactValue : coverCompactType := CoverCompact

def hasFIPType : Type (u + 1) := {X : Type u} → Set (Set X) → Prop
def hasFIPValue : hasFIPType := @HasFIP

def subspaceCompactType : Type (u + 1) :=
  {X : Type u} → [TopologicalSpace X] → Set X → Prop
def subspaceCompactValue : subspaceCompactType := @SubspaceCompact

def ambientCoverCompact_iff_isCompact : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (K : Set X),
    AmbientCoverCompact K ↔ IsCompact K

def coverCompact_iff_isCompact_univ : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    CoverCompact X ↔ IsCompact (univ : Set X)

def coverCompact_iff_compactSpace : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    CoverCompact X ↔ CompactSpace X

def coverCompact_iff_closed_fip : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    CoverCompact X ↔ ∀ A : Set (Set X),
      (∀ F ∈ A, IsClosed F) → HasFIP A → (⋂₀ A).Nonempty

def coverCompact_iff_fip_closures : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    CoverCompact X ↔ ∀ A : Set (Set X),
      HasFIP A → (⋂₀ (closure '' A)).Nonempty

def subspaceCompact_iff_compactSpace : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (K : Set X),
    SubspaceCompact K ↔ CompactSpace K

def subspaceCompact_iff_isCompact : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (K : Set X),
    SubspaceCompact K ↔ IsCompact K

def subspaceCompact_iff_ambient_open_cover : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (K : Set X),
    SubspaceCompact K ↔ ∀ U : Set (Set X),
      (∀ V ∈ U, IsOpen V) → K ⊆ ⋃₀ U →
        ∃ V : Set (Set X), V ⊆ U ∧ V.Finite ∧ K ⊆ ⋃₀ V

def closed_subset_compact : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], CoverCompact X →
    ∀ F : Set X, IsClosed F → SubspaceCompact F

def closed_subset_of_compact : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (K F : Set X),
    SubspaceCompact K → IsClosed F → F ⊆ K → SubspaceCompact F

def finite_union_compact : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set (Set X)),
    A.Finite → (∀ K ∈ A, SubspaceCompact K) → SubspaceCompact (⋃₀ A)

def finite_indexed_union_compact : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {ι : Type v} [Finite ι]
    (K : ι → Set X), (∀ i, SubspaceCompact (K i)) → SubspaceCompact (⋃ i, K i)

def empty_subset_compact : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], SubspaceCompact (∅ : Set X)

def empty_union_compact : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    SubspaceCompact (⋃₀ (∅ : Set (Set X)))

def empty_space_compact : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [IsEmpty X], CoverCompact X

def empty_space_empty_subcover : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [IsEmpty X]
    (U : Set (Set X)),
    (∅ : Set (Set X)) ⊆ U ∧ (∅ : Set (Set X)).Finite ∧
      (univ : Set X) ⊆ ⋃₀ (∅ : Set (Set X))

def fip_empty_family_iff : Prop :=
  ∀ (X : Type u), HasFIP (∅ : Set (Set X)) ↔ Nonempty X

def no_fip_on_empty_space : Prop :=
  ∀ (X : Type u) [IsEmpty X] (A : Set (Set X)), ¬ HasFIP A

end Specs.D10Topology.Ch05.Compactness
