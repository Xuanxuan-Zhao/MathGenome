import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Products

/-! Independent statements for the arbitrary-product assertion in
`paper.tex`, d10:10:product-metric. All topologies are explicit, and
metrizability means existence of a compatible finite real-valued metric.
No assumption on the size of the index type is made. -/

universe u v
namespace Specs.D10Topology.Ch10.ProductMetrization
open Specs.D10Topology.Ch09.MetricConventions
open Specs.D10Topology.Ch03.Products

/-- Under nonemptiness, `Subsingleton (X i)` says that the factor has
exactly one point, since evaluation of a product point inhabits each factor. -/
def product_metrizable_iff : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i)),
    Nonempty (∀ i, X i) →
    (Metrizable (productTopologyValue tX) ↔
      (∀ i, Metrizable (tX i)) ∧ {i : I | ¬ Subsingleton (X i)}.Countable)

/-- The same conclusion with singletons expressed literally by unique existence. -/
def product_metrizable_iff_singletons : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i)),
    Nonempty (∀ i, X i) →
    (Metrizable (productTopologyValue tX) ↔
      (∀ i, Metrizable (tX i)) ∧
        ∃ J : Set I, J.Countable ∧ ∀ i ∉ J, ∃! x : X i, True)

/-- Finite products require no countability exception and may have empty factors. -/
def finite_product_metrizable : Prop :=
  ∀ {I : Type u} {X : I → Type v} [Finite I]
    (tX : ∀ i, TopologicalSpace (X i)),
    (∀ i, Metrizable (tX i)) → Metrizable (productTopologyValue tX)

/-- In particular, the empty index family has its singleton product. -/
def empty_product_metrizable : Prop :=
  ∀ {I : Type u} {X : I → Type v} [IsEmpty I]
    (tX : ∀ i, TopologicalSpace (X i)),
    (∃! x : (∀ i, X i), True) ∧ Metrizable (productTopologyValue tX)

/-- No assumption at all is imposed on any other factor's topology. -/
def empty_factor_product_metrizable : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i))
    (i : I) [IsEmpty (X i)],
    IsEmpty (∀ j, X j) ∧ Metrizable (productTopologyValue tX)

end Specs.D10Topology.Ch10.ProductMetrization
