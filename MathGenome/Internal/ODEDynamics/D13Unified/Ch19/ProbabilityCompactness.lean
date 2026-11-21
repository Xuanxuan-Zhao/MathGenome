import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.ProbabilityCompactness
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Sequences

/-!
Weak sequential compactness of Borel probability measures on a compact metric
space. We use compactness of Mathlib's actual space of probability measures,
its metrizability on a separable metric space, and continuity of integration.
-/

open Filter MeasureTheory Topology

namespace D13Unified.Ch19

/-- `paper.tex`, Lemma `d13:19:probability-compactness`. -/
theorem probability_compactness : Specs.D13Unified.Ch19.ProbabilityCompactness := by
  intro K _ _ _ _ _ ν
  obtain ⟨μ, n, hn, hν⟩ := CompactSpace.tendsto_subseq ν
  refine ⟨n, hn, μ, ?_⟩
  intro g hg
  exact (ProbabilityMeasure.continuous_integral_continuousMap
    (⟨g, hg⟩ : C(K, ℝ))).tendsto μ |>.comp hν

end D13Unified.Ch19
