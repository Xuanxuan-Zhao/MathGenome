import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.MeasureDefinitions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Independent statement of `paper.tex`, Theorem d13:19:unique-ergodic-uniform. -/
open Filter MeasureTheory
open scoped Topology

namespace Specs.D13Unified.Ch19

/-- The real supremum is over all starting points, and the convergence is
asserted separately for every continuous real observable. The hypothesis
specifies an invariant probability and uniqueness among all invariant Borel
probabilities, rather than ergodicity of the selected measure. -/
def UniqueErgodicUniform : Prop :=
  ∀ (K : Type*) [MetricSpace K] [CompactSpace K] [Nonempty K]
    [MeasurableSpace K] [BorelSpace K] (T : K → K), Continuous T →
    ∀ ν : ProbabilityMeasure K,
      MeasureDefinitions.PreservesMeasure T (ν : Measure K) →
      (∀ η : ProbabilityMeasure K,
        MeasureDefinitions.PreservesMeasure T (η : Measure K) → η = ν) →
      ∀ g : K → ℝ, Continuous g →
        Tendsto (fun n : ℕ => ⨆ x : K,
          |MeasureDefinitions.ergodicAverage T g n x - ∫ y, g y ∂(ν : Measure K)|)
          atTop (𝓝 0)

end Specs.D13Unified.Ch19
