import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Foundations
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Path
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Compactification.OnePoint.Sphere

/-!
Independent definitions for the paragraph preceding paper.tex, W62.

A polygonal set is a finite union of closed straight segments. A simple polygonal
arc is such a set that is the image of an injective continuous path with the
specified endpoints. This is an image-based definition: the speed of the path is
unrestricted. Collinear successive segments, arbitrary angles and isolated graph
vertices are allowed. In particular no smoothness or general position is required.

Edges are indexed by the *unordered* edges of the common simple graph. Thus there
is exactly one geometric set per edge, without an orientation or reversal choice.
The only drawing conditions are simplicity/polygonality of each edge, distinct
vertices, and the prescribed incidences/intersections. Faces use actual topological
connected components, with no assumption about their number or their topology.
The compactified plane is identified with the usual unit two-sphere by a library
homeomorphism. No Euler, Jordan, or coloring certificate is part of these data.
-/

universe u
noncomputable section

namespace Specs.FiniteCombinatorics.Graph.Plane.Foundations

abbrev Point := ℝ × ℝ
abbrev Sphere := OnePoint Point

/-- This is a genuine model of the topological two-sphere. -/
def sphereHomeomorph : Sphere ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  onePointEquivSphereOfFinrankEq (by simp [Point])

/-- A finite union, allowing degenerate segments and arbitrary subdivisions. -/
def IsPolygonal (s : Set Point) : Prop :=
  ∃ (n : ℕ) (a b : Fin n → Point), s = ⋃ i, segment ℝ (a i) (b i)

/-- An arc, in the usual topological sense, made of finitely many straight segments. -/
def IsSimplePolygonalArc (a b : Point) (s : Set Point) : Prop :=
  IsPolygonal s ∧ ∃ p : Path a b, Function.Injective p ∧ Set.range p = s

/-- Exactly the geometric data of a finite simple polygonal plane drawing. -/
structure Drawing {V : Type u} [Finite V] (G : SimpleGraph V) where
  point : V → Point
  point_injective : Function.Injective point
  edge : G.edgeSet → Set Point
  edge_arc : ∀ (a b : V) (h : G.Adj a b),
    IsSimplePolygonalArc (point a) (point b) (edge ⟨s(a, b), h⟩)
  vertex_edge : ∀ (e : G.edgeSet) (v : V), point v ∈ edge e ↔ v ∈ e.val
  edge_intersection : ∀ (e f : G.edgeSet), e ≠ f →
    edge e ∩ edge f = point '' {v | v ∈ e.val ∧ v ∈ f.val}

def Planar {V : Type u} [Finite V] (G : SimpleGraph V) : Prop := Nonempty (Drawing G)

def planeImage {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G) : Set Point :=
  Set.range D.point ∪ ⋃ e, D.edge e

/-- Infinity belongs to the ambient sphere, not to the embedded graph. -/
def sphereImage {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G) : Set Sphere :=
  OnePoint.some '' planeImage D

abbrev PlaneComplement {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G) :=
  ↥(planeImage D)ᶜ

abbrev SphereComplement {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G) :=
  ↥(sphereImage D)ᶜ

/-- Plane components are also available, for plane/sphere comparison. -/
def PlaneFace {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G) :=
  ConnectedComponents (PlaneComplement D)

/-- Faces are the connected components of the complement in the sphere. -/
def Face {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G) :=
  ConnectedComponents (SphereComplement D)

/-- The actual subset of the sphere belonging to a face. -/
def faceRegion {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G)
    (F : Face D) : Set Sphere :=
  Subtype.val '' {x : SphereComplement D | ConnectedComponents.mk x = F}

/-- The face selected by infinity. The witness is disjointness from the plane,
not a face-count or separation assumption. -/
def unboundedFace {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G) : Face D :=
  ConnectedComponents.mk ⟨OnePoint.infty, OnePoint.infty_notMem_image_coe⟩

/-- The plane part of the infinity face, the source's unbounded face convention. -/
def unboundedRegion {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G) : Set Point :=
  OnePoint.some ⁻¹' faceRegion D (unboundedFace D)

-- Types used for independent definition-value bindings.
def PointType := Type
def SphereType := Type
def sphereHomeomorphType := Sphere ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
def IsPolygonalType := Set Point → Prop
def IsSimplePolygonalArcType := Point → Point → Set Point → Prop
def PlaneEmbeddingType := ∀ {V : Type u} [Finite V], SimpleGraph V → Type u
def PlaneEmbeddingValue : PlaneEmbeddingType := fun {_} _ G => Drawing G
def PlanarType := ∀ {V : Type u} [Finite V], SimpleGraph V → Prop
def planeImageType := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}, Drawing G → Set Point
def sphereImageType := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}, Drawing G → Set Sphere
def PlaneComplementType := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}, Drawing G → Type
def SphereComplementType := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}, Drawing G → Type
def PlaneFaceType := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}, Drawing G → Type
def FaceType := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}, Drawing G → Type
def faceRegionType := ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G),
  Face D → Set Sphere
def unboundedFaceType := ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G), Face D
def unboundedRegionType := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}, Drawing G → Set Point

-- Full propositions, independent of the implementation.
def polygonal_arc_endpointsType : Prop := ∀ {a b : Point} {s : Set Point},
  IsSimplePolygonalArc a b s → a ∈ s ∧ b ∈ s

def polygonal_arc_reverseType : Prop := ∀ {a b : Point} {s : Set Point},
  IsSimplePolygonalArc a b s → IsSimplePolygonalArc b a s

def vertices_distinctType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G) (a b : V), D.point a = D.point b ↔ a = b

def simple_polygonal_edgeType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G) (a b : V) (h : G.Adj a b),
  IsSimplePolygonalArc (D.point a) (D.point b) (D.edge ⟨s(a, b), h⟩)

def vertex_on_edgeType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G) (a b v : V) (h : G.Adj a b),
  D.point v ∈ D.edge ⟨s(a, b), h⟩ ↔ v = a ∨ v = b

def edge_intersectionType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G) (e f : G.edgeSet), e ≠ f →
  D.edge e ∩ D.edge f = D.point '' {v | v ∈ e.val ∧ v ∈ f.val}

def planar_iffType : Prop := ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  Planar G ↔ Nonempty (Drawing G)

def sphere_image_membershipType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G) (x : Point), OnePoint.some x ∈ sphereImage D ↔ x ∈ planeImage D

def infinity_not_in_imageType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G), OnePoint.infty ∉ sphereImage D

def face_region_componentType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G) (x : SphereComplement D),
  faceRegion D (ConnectedComponents.mk x) = connectedComponentIn (sphereImage D)ᶜ x.val

def face_region_connectedType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G) (F : Face D), IsConnected (faceRegion D F)

def face_region_subsetType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G) (F : Face D), faceRegion D F ⊆ (sphereImage D)ᶜ

def unbounded_face_componentType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G), faceRegion D (unboundedFace D) =
    connectedComponentIn (sphereImage D)ᶜ OnePoint.infty

def unbounded_region_iffType : Prop := ∀ {V : Type u} [Finite V] {G : SimpleGraph V}
  (D : Drawing G) (x : Point), x ∈ unboundedRegion D ↔
    OnePoint.some x ∈ connectedComponentIn (sphereImage D)ᶜ OnePoint.infty

end Specs.FiniteCombinatorics.Graph.Plane.Foundations
