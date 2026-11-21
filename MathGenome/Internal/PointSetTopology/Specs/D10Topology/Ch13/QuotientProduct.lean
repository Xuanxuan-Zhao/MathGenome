import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.QuotientMaps
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.LocalCompactConventions

/-! Independent statement of paper.tex, d10:13:quotient-product.
The quotient predicate includes surjectivity and the open-preimage test.
LCH means one compact neighborhood at each point together with Hausdorffness.
The products have their usual product topologies; no separation, openness,
closedness, or nonemptiness hypothesis is placed on A, B, or q.
-/

universe u v w

namespace Specs.D10Topology.Ch13.QuotientProduct

def quotient_product_lch : Prop :=
  ∀ {X : Type u} {A : Type v} {B : Type w}
    [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
    (q : A → B),
    _root_.D10Topology.Ch03.QuotientData.QuotientMap q →
    Specs.D10Topology.Ch11.LocalCompactConventions.LCH X →
    _root_.D10Topology.Ch03.QuotientData.QuotientMap
      (fun p : X × A => (p.1, q p.2))

end Specs.D10Topology.Ch13.QuotientProduct
