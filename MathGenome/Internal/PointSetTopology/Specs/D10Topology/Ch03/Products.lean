import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.InitialTopologies
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.BasesAndNeighborhoods
import Mathlib.Topology.Bases

/-! Independent specifications for the product and box constructions and their
mapping properties, paper.tex `d10:03:product` and `d10:03:product-universal`.
All topologies are explicit. Empty factors and empty index types are allowed.
The definitions below are expected values; no theorem is assumed. -/

open Set
open scoped Topology
universe u v w

namespace Specs.D10Topology.Ch03.Products

def productType : Type (max (u + 1) (v + 1)) :=
  {I : Type u} → (I → Type v) → Type (max u v)

def productValue : productType.{u, v} := fun X => ∀ i, X i

def projectionType : Type (max (u + 1) (v + 1)) :=
  {I : Type u} → {X : I → Type v} → (i : I) → productValue X → X i

def projectionValue : projectionType.{u, v} := fun i x => x i

def topologyType : Type (max (u + 1) (v + 1)) :=
  {I : Type u} → {X : I → Type v} →
    (∀ i, TopologicalSpace (X i)) → TopologicalSpace (productValue X)

def productTopologyValue : topologyType.{u, v} :=
  fun tX => InitialTopologies.initialTopologyValue tX projectionValue

def basisType : Type (max (u + 1) (v + 1)) :=
  {I : Type u} → {X : I → Type v} →
    (∀ i, TopologicalSpace (X i)) → Set (Set (productValue X))

/-- Finite intersections of inverse images of coordinate opens. The intersection
with no coordinate tests is the whole function space. -/
def productBasisValue : basisType.{u, v} := fun {I} {X} tX =>
  {S | ∃ (U : ∀ i, Set (X i)) (F : Finset I),
    (∀ i ∈ F, IsOpen[tX i] (U i)) ∧ S = (F : Set I).pi U}

/-- Rectangles restricting all coordinates by arbitrary open subsets. -/
def boxBasisValue : basisType.{u, v} := fun {_I} {X} tX =>
  {S | ∃ U : ∀ i, Set (X i), (∀ i, IsOpen[tX i] (U i)) ∧ S = univ.pi U}

def boxTopologyValue : topologyType.{u, v} :=
  fun tX => TopologicalSpace.generateFrom (boxBasisValue tX)

def product_initial : Prop :=
  ∀ {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)),
    productTopologyValue tX = InitialTopologies.initialTopologyValue tX projectionValue

def productTopology_eq_pi : Prop :=
  ∀ {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)),
    productTopologyValue tX = @Pi.topologicalSpace I X tX

def product_basis : Prop :=
  ∀ {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)),
    Specs.D10Topology.Ch01.BasesAndNeighborhoods.basisForValue (productTopologyValue tX) (productBasisValue tX)

def productBasis_intersections : Prop :=
  ∀ {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (S : Set (productValue X)),
    S ∈ productBasisValue tX ↔ ∃ (U : ∀ i, Set (X i)) (F : Finset I),
      (∀ i ∈ F, IsOpen[tX i] (U i)) ∧
        S = ⋂ i ∈ F, projectionValue i ⁻¹' U i

def productBasis_empty : Prop :=
  ∀ {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)),
    univ ∈ productBasisValue tX

def product_opens : Prop :=
  ∀ {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (S : Set (productValue X)),
    IsOpen[productTopologyValue tX] S ↔
      ∃ A : Set (Set (productValue X)), A ⊆ productBasisValue tX ∧ S = ⋃₀ A

def box_basis : Prop :=
  ∀ {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)),
    Specs.D10Topology.Ch01.BasesAndNeighborhoods.basisForValue (boxTopologyValue tX) (boxBasisValue tX)

def box_opens : Prop :=
  ∀ {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (S : Set (productValue X)),
    IsOpen[boxTopologyValue tX] S ↔
      ∃ A : Set (Set (productValue X)), A ⊆ boxBasisValue tX ∧ S = ⋃₀ A

def continuous_product_iff : Prop :=
  ∀ {I : Type u} {X : I → Type v} {Z : Type w}
    (tX : ∀ i, TopologicalSpace (X i)) (tZ : TopologicalSpace Z)
    (g : Z → productValue X),
    Continuous[tZ, productTopologyValue tX] g ↔
      ∀ i, Continuous[tZ, tX i] (projectionValue i ∘ g)

def projection_continuous : Prop :=
  ∀ {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (i : I),
    Continuous[productTopologyValue tX, tX i] (projectionValue i)

def projection_open : Prop :=
  ∀ {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (i : I),
    @IsOpenMap (productValue X) (X i) (productTopologyValue tX) (tX i) (projectionValue i)

def projection_surjective : Prop :=
  ∀ {I : Type u} {X : I → Type v}
    (_h : Nonempty (productValue X)) (i : I),
    Function.Surjective (projectionValue (X := X) i)

def box_eq_product_of_finite : Prop :=
  ∀ {I : Type u} {X : I → Type v} [Finite I]
    (tX : ∀ i, TopologicalSpace (X i)),
    boxTopologyValue tX = productTopologyValue tX

def empty_product_singleton : Prop :=
  ∀ {I : Type u} {X : I → Type v} [IsEmpty I],
    ∃! _x : productValue X, True

def product_empty_of_factor : Prop :=
  ∀ {I : Type u} {X : I → Type v}
    (i : I) [IsEmpty (X i)],
    IsEmpty (productValue X)

end Specs.D10Topology.Ch03.Products
