import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Plane.Foundations
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Homotopy.LocallyContractible

/-! Independent geometric realization interface for paper.tex, W62.
All theorem specifications are definitions of their full proposition types;
none is assumed as a geometric or topological certificate. -/

universe u
noncomputable section

namespace Specs.FiniteCombinatorics.Graph.Plane.RealizationGeometry
open Specs.FiniteCombinatorics.Graph.Plane.Foundations

/-- The embedded graph with its actual subspace topology in the sphere. -/
abbrev Realization {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G) :=
  ↥(sphereImage D)

/-- The original plane realization, useful for its compactification bridge. -/
abbrev PlaneRealization {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G) :=
  ↥(planeImage D)

/-- A graph vertex, as a point of the actual sphere realization. -/
def realizationVertex {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G)
    (v : V) : Realization D :=
  ⟨OnePoint.some (D.point v), D.point v, Or.inl (Set.mem_range_self v), rfl⟩

def realizationVertexType := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G), V → Realization D

def RealizationType := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}, Drawing G → Type
def PlaneRealizationType := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}, Drawing G → Type

def arc_compactType : Prop := ∀ {a b : Point} {s : Set Point},
  IsSimplePolygonalArc a b s → IsCompact s

def arc_intervalType : Prop := ∀ {a b : Point} {s : Set Point},
  IsSimplePolygonalArc a b s → ∃ h : unitInterval ≃ₜ s,
    (h 0).val = a ∧ (h 1).val = b

def edge_compactType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G) (e : G.edgeSet), IsCompact (D.edge e)

def plane_image_compactType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G), IsCompact (planeImage D)

def sphere_image_compactType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G), IsCompact (sphereImage D)

def realization_compactType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G), CompactSpace (Realization D)

def realization_homeomorphType := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G), PlaneRealization D ≃ₜ Realization D

def realization_homeomorphValue : realization_homeomorphType := fun D =>
  OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage (planeImage D)

def realization_properType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G), sphereImage D ≠ Set.univ

def realization_inclusion_properType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V} (D : Drawing G),
  IsProperMap (Subtype.val : Realization D → Sphere)

def realization_nonempty_iffType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V} (D : Drawing G), Nonempty (Realization D) ↔ Nonempty V

def plane_complement_openType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G), IsOpen (planeImage D)ᶜ

def sphere_complement_openType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G), IsOpen (sphereImage D)ᶜ

def plane_complement_locally_path_connectedType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V} (D : Drawing G), LocallyPathConnectedSpace (PlaneComplement D)

def sphere_complement_locally_path_connectedType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V} (D : Drawing G), LocallyPathConnectedSpace (SphereComplement D)

def complement_path_componentType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V} (D : Drawing G) (x : SphereComplement D),
  pathComponent x = connectedComponent x

/-- Correspondence agrees with the original graph vertices, hence includes isolated vertices. -/
def realization_componentsType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V} (D : Drawing G),
  ∃ E : ConnectedComponents (Realization D) ≃ G.ConnectedComponent,
    ∀ v : V, E (ConnectedComponents.mk (realizationVertex D v)) = G.connectedComponentMk v

def realization_vertex_componentsType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V} (D : Drawing G) (a b : V),
  ConnectedComponents.mk (realizationVertex D a) =
    ConnectedComponents.mk (realizationVertex D b) ↔ G.Reachable a b

/-- The full interior of an edge is an open interval in the actual realization. -/
def edge_interior_local_modelType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V} (D : Drawing G) (e : G.edgeSet),
  ∃ U : Set (Realization D), IsOpen U ∧
    (∀ x, x ∈ U ↔ ∃ y ∈ D.edge e, y ∉ Set.range D.point ∧ x.val = OnePoint.some y) ∧
    Nonempty (U ≃ₜ ↥(Set.Ioo (0 : ℝ) 1))

/-- A vertex of degree zero has a one-point open neighborhood. -/
def isolated_vertex_local_modelType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V} (D : Drawing G) (v : V), G.IsIsolated v →
    IsOpen ({realizationVertex D v} : Set (Realization D))

/-- A compact finite star with exactly n arms, including the single point when n=0. -/
def finiteStar (n : ℕ) : Set (Fin n → ℝ) :=
  {0} ∪ ⋃ i : Fin n, segment ℝ 0 (Pi.single i 1)

def finite_star_contractibleType : Prop := ∀ n : ℕ, ContractibleSpace (finiteStar n)

/-- Arbitrarily small star neighborhoods at every vertex, with the center fixed.
Neighborhoods may be closed; the compact model includes the outer arm ends. -/
def vertex_star_local_modelType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V} (D : Drawing G) (v : V) (U : Set (Realization D)),
  U ∈ nhds (realizationVertex D v) →
    ∃ N : Set (Realization D), N ∈ nhds (realizationVertex D v) ∧ N ⊆ U ∧
      ∃ (hv : realizationVertex D v ∈ N)
        (h : N ≃ₜ ↥(finiteStar (Nat.card (G.neighborSet v)))),
        (h ⟨realizationVertex D v, hv⟩).val = 0

def realization_locally_contractibleType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V} (D : Drawing G), LocallyContractibleSpace (Realization D)

/-- The geometric inclusion of the plane complement in the sphere complement. -/
def complementInclusion {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : Drawing G) (x : PlaneComplement D) : SphereComplement D :=
  ⟨OnePoint.some x.val, by
    rintro ⟨y, hy, heq⟩
    exact x.property (OnePoint.coe_injective heq ▸ hy)⟩

def planeFaceRegion {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : Drawing G) (F : PlaneFace D) : Set Point :=
  Subtype.val '' {x : PlaneComplement D | ConnectedComponents.mk x = F}

/-- Adding infinity preserves the components of the plane complement, and
exactly one plane component is unbounded. -/
def plane_sphere_facesType : Prop := ∀ {V : Type u} [Finite V]
  {G : SimpleGraph V} (D : Drawing G),
  ∃ E : PlaneFace D ≃ Face D,
    (∀ x : PlaneComplement D,
      E (ConnectedComponents.mk x) = ConnectedComponents.mk (complementInclusion D x)) ∧
    (∀ F : PlaneFace D,
      OnePoint.some '' planeFaceRegion D F = faceRegion D (E F) \ {OnePoint.infty}) ∧
    (∀ F : PlaneFace D,
      E F = unboundedFace D ↔ ¬Bornology.IsBounded (planeFaceRegion D F))

end Specs.FiniteCombinatorics.Graph.Plane.RealizationGeometry
