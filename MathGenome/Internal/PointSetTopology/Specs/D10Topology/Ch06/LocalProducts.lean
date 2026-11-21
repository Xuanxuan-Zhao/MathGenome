import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.LocalConnectedness
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness

/-! Independent statements for paper.tex, `d10:06:local-products`.
The product has the canonical source product topology. The product alone is
assumed nonempty; the index type may be empty. Exceptional sets are sets of
indices, so repeated factors are counted separately. Source connectedness and
path connectedness both allow the empty space. Components are the source's
maximal connected subsets, represented as a range of sets. -/

open Set
universe u v

namespace Specs.D10Topology.Ch06.LocalProducts
open _root_.D10Topology.Ch06.LocalConnectednessData
open _root_.D10Topology.Ch06.ConnectednessData
open _root_.D10Topology.Ch06.ComponentsPathsData

/-- Local connectedness of a nonempty arbitrary indexed product. -/
def locallyConnected_product_iff : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i)),
    Nonempty (∀ i, X i) →
    (@LocallyConnected (∀ i, X i) (Ch03.Products.productTopologyValue tX) ↔
      (∀ i, @LocallyConnected (X i) (tX i)) ∧
        {i | ¬ @Connected (X i) (tX i)}.Finite)

/-- The parallel characterization for local path connectedness. -/
def locallyPathConnected_product_iff : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i)),
    Nonempty (∀ i, X i) →
    (@LocallyPathConnected (∀ i, X i) (Ch03.Products.productTopologyValue tX) ↔
      (∀ i, @LocallyPathConnected (X i) (tX i)) ∧
        {i | ¬ @PathConnected (X i) (tX i)}.Finite)

/-- No Hausdorffness or nonemptiness is imposed on the compact space. -/
def finite_components_of_compact_locallyConnected : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    Ch05.Compactness.CoverCompact X → LocallyConnected X →
      (range (Component : X → Set X)).Finite

/-- In the empty case there are zero components. -/
def components_of_empty : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [IsEmpty X],
    range (Component : X → Set X) = ∅

end Specs.D10Topology.Ch06.LocalProducts
