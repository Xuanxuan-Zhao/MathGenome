import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.BasesAndNeighborhoods
import Mathlib.Order.Filter.Bases.Finite
import Mathlib.Topology.ClusterPt

open Set Filter
open scoped Topology
universe u v

namespace Specs.D10Topology.Ch04.ProperFilters

def ProperFilter (X : Type u) : Type u :=
  {F : Filter X // F.NeBot}

def ProperFamily {X : Type u} (A : Set (Set X)) : Prop :=
  A.Nonempty ∧ (∅ : Set X) ∉ A ∧
    (∀ U ∈ A, ∀ V, U ⊆ V → V ∈ A) ∧
    (∀ U ∈ A, ∀ V ∈ A, U ∩ V ∈ A)

def FilterBase {X : Type u} (B : Set (Set X)) : Prop :=
  B.Nonempty ∧ (∀ U ∈ B, U.Nonempty) ∧
    ∀ U ∈ B, ∀ V ∈ B, ∃ W ∈ B, W ⊆ U ∩ V

def FiniteIntersectionProperty {X : Type u} (A : Set (Set X)) : Prop :=
  ∀ C : Set (Set X), C ⊆ A → C.Finite → (⋂₀ C).Nonempty

def GeneratedFilter {X : Type u} (A : Set (Set X)) : Filter X :=
  Filter.generate A

def FilterFiner {X : Type u} (G F : Filter X) : Prop :=
  F.sets ⊆ G.sets

def ImageFilter {X : Type u} {Y : Type v} (f : X → Y) (F : Filter X) : Filter Y :=
  Filter.map f F

def FilterConverges {X : Type u} [t : TopologicalSpace X] (F : Filter X) (x : X) : Prop :=
  ∀ N : Set X, _root_.Specs.D10Topology.Ch01.BasesAndNeighborhoods.Neighborhood t x N → N ∈ F

def FilterClusters {X : Type u} [t : TopologicalSpace X] (F : Filter X) (x : X) : Prop :=
  ∀ U ∈ F, ∀ N : Set X, _root_.Specs.D10Topology.Ch01.BasesAndNeighborhoods.Neighborhood t x N → (U ∩ N).Nonempty

def ProperFilterType : Type (u + 1) := (X : Type u) → Type u
def ProperFilterValue : ProperFilterType := @ProperFilter

def ProperFamilyType : Type (u + 1) := {X : Type u} → Set (Set X) → Prop
def ProperFamilyValue : ProperFamilyType := @ProperFamily

def FilterBaseType : Type (u + 1) := {X : Type u} → Set (Set X) → Prop
def FilterBaseValue : FilterBaseType := @FilterBase

def FiniteIntersectionPropertyType : Type (u + 1) := {X : Type u} → Set (Set X) → Prop
def FiniteIntersectionPropertyValue : FiniteIntersectionPropertyType := @FiniteIntersectionProperty

def GeneratedFilterType : Type (u + 1) := {X : Type u} → Set (Set X) → Filter X
def GeneratedFilterValue : GeneratedFilterType := @GeneratedFilter

def FilterFinerType : Type (u + 1) := {X : Type u} → Filter X → Filter X → Prop
def FilterFinerValue : FilterFinerType := @FilterFiner

def ImageFilterType : Type (max (u + 1) (v + 1)) := {X : Type u} → {Y : Type v} → (X → Y) → Filter X → Filter Y
def ImageFilterValue : ImageFilterType := @ImageFilter

def FilterConvergesType : Type (u + 1) := {X : Type u} → [TopologicalSpace X] → Filter X → X → Prop
def FilterConvergesValue : FilterConvergesType := @FilterConverges

def FilterClustersType : Type (u + 1) := {X : Type u} → [TopologicalSpace X] → Filter X → X → Prop
def FilterClustersValue : FilterClustersType := @FilterClusters

def properFamily_iff_filter : Prop :=
  ∀ {X : Type u} (A : Set (Set X)), ProperFamily A ↔
  ∃! F : Filter X, F.sets = A ∧ F.NeBot

def proper_iff_empty_not_mem : Prop :=
  ∀ {X : Type u} (F : Filter X), F.NeBot ↔ (∅ : Set X) ∉ F

def filter_finite_intersections : Prop :=
  ∀ {X : Type u} (F : Filter X) (C : Set (Set X)), C.Finite →
  C ⊆ F.sets → ⋂₀ C ∈ F

def finer_iff_le : Prop :=
  ∀ {X : Type u} (G F : Filter X), FilterFiner G F ↔ G ≤ F

def generated_mem : Prop :=
  ∀ {X : Type u} (A : Set (Set X)) (U : Set X),
  U ∈ GeneratedFilter A ↔ ∃ C ⊆ A, C.Finite ∧ ⋂₀ C ⊆ U

def generated_contains : Prop :=
  ∀ {X : Type u} (A : Set (Set X)), A ⊆ (GeneratedFilter A).sets

def generated_smallest : Prop :=
  ∀ {X : Type u} (A : Set (Set X)) (F : Filter X),
  A ⊆ F.sets → FilterFiner F (GeneratedFilter A)

def base_generated_mem : Prop :=
  ∀ {X : Type u} (B : Set (Set X)), FilterBase B → ∀ U : Set X,
  U ∈ GeneratedFilter B ↔ ∃ V ∈ B, V ⊆ U

def base_generates_proper : Prop :=
  ∀ {X : Type u} (B : Set (Set X)), FilterBase B → (GeneratedFilter B).NeBot

def generated_proper_iff_fip : Prop :=
  ∀ {X : Type u} (A : Set (Set X)),
  (GeneratedFilter A).NeBot ↔ FiniteIntersectionProperty A

def fip_iff_contained_in_proper : Prop :=
  ∀ {X : Type u} (A : Set (Set X)),
  FiniteIntersectionProperty A ↔ ∃ F : Filter X, F.NeBot ∧ A ⊆ F.sets

def no_proper_filter_on_empty : Prop :=
  ∀ {X : Type u} [IsEmpty X], IsEmpty (ProperFilter X)

def neighborhood_filter_proper : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (x : X), (nhds x).NeBot

def neighborhood_filter_family : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (x : X),
  (nhds x).sets = {N | _root_.Specs.D10Topology.Ch01.BasesAndNeighborhoods.Neighborhood t x N}

def image_mem : Prop :=
  ∀ {X : Type u} {Y : Type v} (f : X → Y) (F : Filter X) (B : Set Y),
  B ∈ ImageFilter f F ↔ f ⁻¹' B ∈ F

def image_proper : Prop :=
  ∀ {X : Type u} {Y : Type v} (f : X → Y) (F : Filter X) [F.NeBot],
  (ImageFilter f F).NeBot

def image_generated_mem : Prop :=
  ∀ {X : Type u} {Y : Type v} (f : X → Y) (F : Filter X) (B : Set Y),
  B ∈ ImageFilter f F ↔ ∃ A ∈ F, f '' A ⊆ B

def image_sets_base : Prop :=
  ∀ {X : Type u} {Y : Type v} (f : X → Y) (F : Filter X) [F.NeBot],
  FilterBase ((fun A : Set X => f '' A) '' F.sets)

def image_eq_generated : Prop :=
  ∀ {X : Type u} {Y : Type v} (f : X → Y) (F : Filter X),
  ImageFilter f F = GeneratedFilter ((fun A : Set X => f '' A) '' F.sets)

def converges_iff_le_nhds : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (F : Filter X) (x : X),
  FilterConverges F x ↔ F ≤ nhds x

def clusters_iff_clusterPt : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (F : Filter X) (x : X),
  FilterClusters F x ↔ ClusterPt x F

def clusters_iff_closures : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (F : Filter X) (x : X),
  FilterClusters F x ↔ x ∈ ⋂ U ∈ F, closure U

def clusters_iff_finer_converges : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (F : Filter X) [F.NeBot] (x : X),
  FilterClusters F x ↔ ∃ G : Filter X, G.NeBot ∧ FilterFiner G F ∧ FilterConverges G x

def closure_iff_proper_filter : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (A : Set X) (x : X),
  x ∈ closure A ↔ ∃ F : Filter X, F.NeBot ∧ A ∈ F ∧ FilterConverges F x

def continuousAt_iff_filters : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (f : X → Y) (x : X), ContinuousAt f x ↔
  ∀ F : Filter X, F.NeBot → FilterConverges F x → FilterConverges (ImageFilter f F) (f x)

def continuousAt_iff_nhds_image : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (f : X → Y) (x : X), ContinuousAt f x ↔ FilterConverges (ImageFilter f (nhds x)) (f x)

end Specs.D10Topology.Ch04.ProperFilters
