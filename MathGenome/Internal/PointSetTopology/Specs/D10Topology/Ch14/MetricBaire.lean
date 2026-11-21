import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch14.CategoryInterface
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions

/-! Independent statements of paper.tex, d10:14:baire-metric.
Completeness is the source's Cauchy-sequence condition for the specified
metric. Complete metrizability is existence of a compatible complete metric.
Neither statement requires the underlying space to be nonempty. -/

universe u

namespace Specs.D10Topology.Ch14.MetricBaire

def complete_metric_baire : Prop :=
  ∀ {X : Type u} (d : MetricSpace X),
    Ch09.MetricConventions.SequentiallyComplete d.toPseudoMetricSpace →
      @CategoryInterface.baireValue X
        (Ch09.MetricConventions.metricTopology d.toPseudoMetricSpace)

def completely_metrizable_baire : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X),
    Ch09.MetricConventions.CompletelyMetrizable t →
      @CategoryInterface.baireValue X t

end Specs.D10Topology.Ch14.MetricBaire
