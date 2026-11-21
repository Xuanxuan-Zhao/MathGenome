import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Products

/-!
Independent specifications for the arbitrary-product part of
`paper.tex`, d10:07:heredity-products. The topology is the initial
topology of the coordinate projections, as fixed in Chapter 3.
There are no nonemptiness hypotheses on the index type or the factors.
Regularity and complete regularity do not include T1.
-/

universe u v

namespace Specs.D10Topology.Ch07.SeparationProducts

open SeparationConventions
open Specs.D10Topology.Ch03.Products

def product_t0 : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i)),
    (∀ i, @t0Value (X i) (tX i)) →
      @t0Value (productValue X) (productTopologyValue tX)

def product_t1 : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i)),
    (∀ i, @t1Value (X i) (tX i)) →
      @t1Value (productValue X) (productTopologyValue tX)

def product_t2 : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i)),
    (∀ i, @t2Value (X i) (tX i)) →
      @t2Value (productValue X) (productTopologyValue tX)

def product_regular : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i)),
    (∀ i, @regularValue (X i) (tX i)) →
      @regularValue (productValue X) (productTopologyValue tX)

/-- Full point-versus-closed-set separation on the product, with the
paper's values 1 at the point and 0 on the closed set. -/
def product_completelyRegular : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i)),
    (∀ i, @completelyRegularValue (X i) (tX i)) →
      @completelyRegularValue (productValue X) (productTopologyValue tX)

def product_t3 : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i)),
    (∀ i, @t3Value (X i) (tX i)) →
      @t3Value (productValue X) (productTopologyValue tX)

def product_tychonoff : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i)),
    (∀ i, @tychonoffValue (X i) (tX i)) →
      @tychonoffValue (productValue X) (productTopologyValue tX)

end Specs.D10Topology.Ch07.SeparationProducts
