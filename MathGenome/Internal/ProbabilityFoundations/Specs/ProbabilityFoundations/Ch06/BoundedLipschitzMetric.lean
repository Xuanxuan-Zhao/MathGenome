import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.WeakMetrics

/-!
The bounded Lipschitz part of `thm:p06-weak-metrics` (paper.tex 2052–2075,
2102–2113). The distance is the upstream real supremum with separate
unit bounds. The metric topology maps continuously to the topology generated
by all bounded continuous real integral tests. No separability or tightness
hypothesis is imposed, and the convergence statement allows every filter.
-/

open MeasureTheory Filter Topology

namespace Specs.ProbabilityFoundations.Ch06.BoundedLipschitzMetric

universe u v
noncomputable section

def metricAndContinuityType : Prop :=
  ∀ {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S],
    ∃ m : MetricSpace (ProbabilityMeasure S),
      (∀ μ ν, @dist _ m.toDist μ ν = WeakMetrics.boundedLipschitzDistValue μ ν) ∧
      @Continuous (ProbabilityMeasure S) (ProbabilityMeasure S)
        m.toUniformSpace.toTopologicalSpace
        (WeakFramework.weakTopologyValue (S := S)) id

def convergenceType : Prop :=
  ∀ {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    {ι : Type v} (l : Filter ι) (μs : ι → ProbabilityMeasure S) (μ : ProbabilityMeasure S),
    Tendsto (fun i => WeakMetrics.boundedLipschitzDistValue (μs i) μ) l (𝓝 0) →
    Tendsto μs l (𝓝 μ)

end
end Specs.ProbabilityFoundations.Ch06.BoundedLipschitzMetric
