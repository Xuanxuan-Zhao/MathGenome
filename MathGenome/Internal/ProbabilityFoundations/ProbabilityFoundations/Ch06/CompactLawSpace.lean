import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.WeakFramework
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.CompactLawSpace
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Probability laws on a compact metric space

Lemma 6.12, paper.tex lines 1749–1783. Mathlib proves compactness via
compact Riesz representation. Its Lévy–Prokhorov metrization applies because
a compact metric space is separable. The upstream topology identification
transfers both facts to the initial topology of bounded continuous real tests.
Neither proof selects a point or a probability law on the underlying space.
-/

open MeasureTheory TopologicalSpace

namespace ProbabilityFoundations.Ch06

universe u

/-- The Borel probability-law space of any compact metric space is weakly compact. -/
theorem compactLawSpace {H : Type u} [MetricSpace H] [CompactSpace H]
    [MeasurableSpace H] [BorelSpace H] :
    @CompactSpace (ProbabilityMeasure H) (weakTopology (S := H)) := by
  rw [weakTopology_eq]
  infer_instance

/-- The weak topology on these laws is metrizable; the empty base is allowed. -/
theorem metrizableLawSpace {H : Type u} [MetricSpace H] [CompactSpace H]
    [MeasurableSpace H] [BorelSpace H] :
    @MetrizableSpace (ProbabilityMeasure H) (weakTopology (S := H)) := by
  have : SeparableSpace H := inferInstance
  rw [weakTopology_eq]
  infer_instance

end ProbabilityFoundations.Ch06
