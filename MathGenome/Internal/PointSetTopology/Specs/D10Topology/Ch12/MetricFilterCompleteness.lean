import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformConventions

/-!
Independent statements for paper.tex, Proposition `d10:12:metric-completeness`.
The uniformity is the one belonging to the displayed metric, and the right-hand
side is exactly Chapter 9's epsilon definition of sequential completeness.
`Complete` quantifies over proper Cauchy filters and uses neighborhood-filter
convergence. No nonemptiness hypothesis is imposed.
-/

universe u

namespace Specs.D10Topology.Ch12.MetricFilterCompleteness

/-- Filter completeness of a metric uniformity equals sequential completeness
for that same metric, including the empty space. -/
def metric_complete_iff_sequentiallyComplete : Prop :=
  ∀ {X : Type u} (d : MetricSpace X),
    @UniformConventions.Complete X d.toUniformSpace ↔
      Ch09.MetricConventions.SequentiallyComplete d.toPseudoMetricSpace

/-- Both completeness formulations hold vacuously on every empty metric space. -/
def metric_complete_empty : Prop :=
  ∀ {X : Type u} [IsEmpty X] (d : MetricSpace X),
    @UniformConventions.Complete X d.toUniformSpace ∧
      Ch09.MetricConventions.SequentiallyComplete d.toPseudoMetricSpace

end Specs.D10Topology.Ch12.MetricFilterCompleteness
