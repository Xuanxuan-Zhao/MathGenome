import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.Connectedness
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Products

/-! Independent statements for paper.tex `d10:06:product`.
The shared connectedness predicate means absence of a separation, so it
includes empty spaces. The topology is the shared initial product topology.
No inhabitedness, separation, or finiteness assumption is made in the forward
direction. Only the converse requires a nonempty product. -/

universe u v

namespace Specs.D10Topology.Ch06.ConnectedProducts

open _root_.D10Topology.Ch06.ConnectednessData
open Specs.D10Topology.Ch03.Products

def connected_product : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i)),
    (∀ i, @Connected (X i) (tX i)) →
      @Connected (productValue X) (productTopologyValue tX)

def connected_factor_of_product : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i)),
    Nonempty (productValue X) →
      @Connected (productValue X) (productTopologyValue tX) →
        ∀ i, @Connected (X i) (tX i)

def connected_product_iff : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i)),
    Nonempty (productValue X) →
      (@Connected (productValue X) (productTopologyValue tX) ↔
        ∀ i, @Connected (X i) (tX i))

/-- The empty-index product has one point, independently of the factors. -/
def connected_empty_product : Prop :=
  ∀ {I : Type u} {X : I → Type v} [IsEmpty I]
    (tX : ∀ i, TopologicalSpace (X i)),
    @Connected (productValue X) (productTopologyValue tX)

/-- An empty factor makes the whole product empty. The other factors may
be disconnected, so no connectedness assumption on them is imposed here. -/
def connected_product_of_empty_factor : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i))
    (i : I) [IsEmpty (X i)],
    @Connected (productValue X) (productTopologyValue tX)

end Specs.D10Topology.Ch06.ConnectedProducts
