import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.ProkhorovMetric
import Mathlib.Topology.MetricSpace.Polish

/-! Completeness in Theorem `thm:p06-polish-laws`, paper.tex 2208–2256.
The uniform structure is that of the specified source Prokhorov metric.
No nonemptiness hypothesis is imposed on the state or law space. -/
open MeasureTheory Filter Topology TopologicalSpace
namespace Specs.ProbabilityFoundations.Ch06.LawSpaceCompleteness
universe u
noncomputable section

def completeType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] [SeparableSpace S] [CompleteSpace S],
  @CompleteSpace (ProbabilityMeasure S)
    (ProkhorovMetric.metricSpaceValue (S := S)).toUniformSpace

def sequenceType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] [SeparableSpace S] [CompleteSpace S]
  (μ : ℕ → ProbabilityMeasure S),
  (∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
    WeakMetrics.prokhorovDistValue (μ m) (μ n) < ε) →
  ∃ ν : ProbabilityMeasure S,
    Tendsto (fun n => WeakMetrics.prokhorovDistValue (μ n) ν) atTop (𝓝 0)

def polishType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] [SeparableSpace S] [CompleteSpace S],
  @PolishSpace (ProbabilityMeasure S) (WeakFramework.weakTopologyValue (S := S))

end
end Specs.ProbabilityFoundations.Ch06.LawSpaceCompleteness
