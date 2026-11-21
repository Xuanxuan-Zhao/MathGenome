import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.MetricFilterCompleteness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.UniformConventions

/-!
Proposition `d10:12:metric-completeness` in paper.tex.

Chapter 12's `complete_iff_mathlib` identifies the proper-small-square filter
condition and neighborhood convergence with `CompleteSpace`. Chapter 9's
`sequentiallyComplete_iff_mathlib` identifies its epsilon sequence definition
with `CompleteSpace` for the displayed metric. Composing these proved bridges
uses precisely the metric's uniformity and topology. In particular there is no
assumption of a complete metric, and no change of compatible metric.
-/

universe u

namespace D10Topology.Ch12

/-- A metric uniformity is complete exactly when every Cauchy sequence converges
in the Chapter 9 sense, with no restriction on the underlying space. -/
theorem metric_complete_iff_sequentiallyComplete {X : Type u} (d : MetricSpace X) :
    @Complete X d.toUniformSpace ↔
      Ch09.SequentiallyComplete d.toPseudoMetricSpace := by
  let : MetricSpace X := d
  exact (complete_iff_mathlib (X := X)).trans
    (Ch09.sequentiallyComplete_iff_mathlib d.toPseudoMetricSpace).symm

/-- Empty metric spaces are complete in both the proper-filter and sequence
senses: there are neither proper Cauchy filters nor sequences in them. -/
theorem metric_complete_empty {X : Type u} [IsEmpty X] (d : MetricSpace X) :
    @Complete X d.toUniformSpace ∧
      Ch09.SequentiallyComplete d.toPseudoMetricSpace := by
  let : MetricSpace X := d
  exact ⟨complete_empty, Ch09.empty_complete d.toPseudoMetricSpace⟩

end D10Topology.Ch12
