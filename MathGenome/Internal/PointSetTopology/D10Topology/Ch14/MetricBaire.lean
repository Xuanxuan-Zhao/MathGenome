import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch14.MetricBaire
import MathGenome.Internal.PointSetTopology.D10Topology.Ch14.CategoryInterface
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricConventions
import Mathlib.Topology.Baire.CompleteMetrizable

/-! Baire's theorem for complete metrics and completely metrizable topologies
(paper.tex, d10:14:baire-metric). The library theorem is proved by shrinking
closed balls and convergence of their Cauchy centers; it assumes no Baire
hypothesis. The accepted bridges identify both sequence completeness and
the countable-family Baire property with the library formulations. -/

universe u

namespace D10Topology.Ch14

/-- Every complete metric space is Baire, including the empty space. -/
theorem complete_metric_baire {X : Type u} (d : MetricSpace X)
    (hc : Ch09.SequentiallyComplete d.toPseudoMetricSpace) :
    @BaireIn X (Ch09.metricTopology d.toPseudoMetricSpace) := by
  letI := d
  letI : CompleteSpace X := (Ch09.sequentiallyComplete_iff_mathlib _).mp hc
  exact (baire_iff_library X).mpr inferInstance

/-- It is enough that some compatible metric is complete. No completeness
condition is placed on any other metric inducing the topology. -/
theorem completely_metrizable_baire {X : Type u} (t : TopologicalSpace X)
    (hc : Ch09.CompletelyMetrizable t) : @BaireIn X t := by
  obtain ⟨d, ht, hd⟩ := hc
  rw [← ht]
  exact complete_metric_baire d hd

end D10Topology.Ch14
