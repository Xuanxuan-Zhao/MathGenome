import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.CountabilityConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Products

/-!
Independent statements of the countable-product assertions in
paper.tex, `d10:08:permanence` (lines 1044–1051).

The index type is at most countable, so finite and empty index families
are included. The factors need not be nonempty and have no separation
assumptions. Products carry the upstream product topology, defined as
the initial topology of the coordinate projections.
-/

universe u v

namespace Specs.D10Topology.Ch08.CountableProducts

def countable_product_firstCountable : Prop :=
  ∀ {I : Type u} [Countable I] {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)),
    (∀ i, Ch04.FirstCountableSequences.FirstCountable (tX i)) →
      Ch04.FirstCountableSequences.FirstCountable
        (Ch03.Products.productTopologyValue tX)

def countable_product_secondCountable : Prop :=
  ∀ {I : Type u} [Countable I] {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)),
    (∀ i, @SecondCountableTopology (X i) (tX i)) →
      @SecondCountableTopology (Ch03.Products.productValue X)
        (Ch03.Products.productTopologyValue tX)

def countable_product_separable : Prop :=
  ∀ {I : Type u} [Countable I] {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)),
    (∀ i, @TopologicalSpace.SeparableSpace (X i) (tX i)) →
      @TopologicalSpace.SeparableSpace (Ch03.Products.productValue X)
        (Ch03.Products.productTopologyValue tX)

end Specs.D10Topology.Ch08.CountableProducts
