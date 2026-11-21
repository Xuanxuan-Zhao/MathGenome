import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Products
import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-! Independent statements for the explicit metric in d10:10:product-metric.
Coordinate `n : ℕ` represents the paper's coordinate `n+1`, so the weight is
`(2⁻¹)^(n+1)`. No factor, or product, is required to be nonempty. -/

universe u
namespace Specs.D10Topology.Ch10.CountableProductMetric
open Specs.D10Topology.Ch09.MetricConventions

def productDistanceType :=
  {X : ℕ → Type u} → (∀ n, MetricSpace (X n)) → (∀ n, X n) → (∀ n, X n) → ℝ

noncomputable def productDistanceValue : productDistanceType := fun d x y =>
  ∑' n : ℕ, (2⁻¹ : ℝ) ^ (n + 1) * min 1 (distance (d n).toPseudoMetricSpace (x n) (y n))

def product_series_summable : Prop :=
  ∀ {X : ℕ → Type u} (d : ∀ n, MetricSpace (X n)) (x y : ∀ n, X n),
    Summable (fun n : ℕ => (2⁻¹ : ℝ) ^ (n + 1) *
      min 1 (distance (d n).toPseudoMetricSpace (x n) (y n)))

/-- The metric is required to have exactly the displayed distance. Its topology
is the previously specified product topology, and completeness concerns this
metric, not just the existence of a complete compatible metric. -/
def product_metric_exists : Prop :=
  ∀ {X : ℕ → Type u} (d : ∀ n, MetricSpace (X n)),
    ∃ m : MetricSpace (∀ n, X n),
      distance m.toPseudoMetricSpace = productDistanceValue d ∧
      metricTopology m.toPseudoMetricSpace =
        Specs.D10Topology.Ch03.Products.productTopologyValue
          (fun n => metricTopology (d n).toPseudoMetricSpace) ∧
      ((∀ n, SequentiallyComplete (d n).toPseudoMetricSpace) →
        SequentiallyComplete m.toPseudoMetricSpace)

end Specs.D10Topology.Ch10.CountableProductMetric
