import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.QuotientMaps
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Products
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Subspaces

/-!
Independent statements for paper.tex, `d10:03:quotient-restriction`.
`B.restrictPreimage q` is the map `q ⁻¹' B → B`, with both subtypes
carrying their induced topologies. Its domain is the full inverse image,
not an arbitrary subset of X. The product uses the canonical dependent
product topology, identified with the source's initial topology in Products.
No separation, nonemptiness, or finiteness assumptions are imposed.
-/

open Set Topology
universe u v w

namespace Specs.D10Topology.Ch03.QuotientRestrictions
open _root_.D10Topology.Ch03.QuotientData

def quotient_restrictPreimage_of_isOpen : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (q : X → Y) (B : Set Y), QuotientMap q → IsOpen (q ⁻¹' B) →
      QuotientMap (B.restrictPreimage q)

def quotient_restrictPreimage_of_isClosed : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (q : X → Y) (B : Set Y), QuotientMap q → IsClosed (q ⁻¹' B) →
      QuotientMap (B.restrictPreimage q)

def open_quotient_restrictPreimage : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (q : X → Y) (B : Set Y), QuotientMap q → IsOpenMap q →
      IsOpenMap (B.restrictPreimage q) ∧ QuotientMap (B.restrictPreimage q)

def closed_quotient_restrictPreimage : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (q : X → Y) (B : Set Y), QuotientMap q → IsClosedMap q →
      IsClosedMap (B.restrictPreimage q) ∧ QuotientMap (B.restrictPreimage q)

/-- Arbitrary products, including empty index types and empty factors.
Choice is permitted by foundation F1. -/
def product_open_surjections : Prop :=
  ∀ {I : Type u} {X : I → Type v} {Y : I → Type w}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (q : ∀ i, X i → Y i),
    (∀ i, Continuous (q i)) → (∀ i, IsOpenMap (q i)) →
    (∀ i, Function.Surjective (q i)) →
      Continuous (Pi.map q) ∧ IsOpenMap (Pi.map q) ∧
        Function.Surjective (Pi.map q) ∧ QuotientMap (Pi.map q)

end Specs.D10Topology.Ch03.QuotientRestrictions
