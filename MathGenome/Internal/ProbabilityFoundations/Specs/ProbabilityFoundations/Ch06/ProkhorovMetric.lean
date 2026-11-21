import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.WeakMetrics
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
The π part of paper.tex, Theorem 6.18 (2052–2075, 2102–2113).
All metric spaces and all Borel probability laws are included. The metric
structure is transported from the library's law-space synonym; its distance is
required below to equal the original positive-radius real infimum. Continuity
has the initial weak topology as its codomain and hence includes arbitrary nets.
-/

open MeasureTheory Filter Topology

namespace Specs.ProbabilityFoundations.Ch06.ProkhorovMetric

universe u v
noncomputable section
open WeakMetrics WeakFramework

def metricSpaceType := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S], MetricSpace (ProbabilityMeasure S)

def metricSpaceValue : metricSpaceType := fun {S} _ _ _ =>
  MetricSpace.induced (LevyProkhorov.ofMeasure : ProbabilityMeasure S →
    LevyProkhorov (ProbabilityMeasure S))
    (fun _ _ h => congrArg LevyProkhorov.toMeasure h) inferInstance

def distanceIdentificationType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S),
  prokhorovDistValue μ ν = levyProkhorovDist (μ : Measure S) (ν : Measure S)

def metricDistanceType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S),
  @dist _ (metricSpaceValue (S := S)).toDist μ ν = prokhorovDistValue μ ν

def nonnegType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S),
  0 ≤ prokhorovDistValue μ ν

def selfType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (μ : ProbabilityMeasure S),
  prokhorovDistValue μ μ = 0

def commType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S),
  prokhorovDistValue μ ν = prokhorovDistValue ν μ

def eqZeroType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S),
  prokhorovDistValue μ ν = 0 ↔ μ = ν

def triangleType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (μ ν κ : ProbabilityMeasure S),
  prokhorovDistValue μ κ ≤ prokhorovDistValue μ ν + prokhorovDistValue ν κ

def continuousIdentityType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S],
  @Continuous (ProbabilityMeasure S) (ProbabilityMeasure S)
    (metricSpaceValue (S := S)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    (weakTopologyValue (S := S)) id

def convergenceType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] {ι : Type v} (l : Filter ι)
  (μs : ι → ProbabilityMeasure S) (μ : ProbabilityMeasure S),
  Tendsto (fun i => prokhorovDistValue (μs i) μ) l (𝓝 0) →
    weaklyConvergesValue l μs μ

end
end Specs.ProbabilityFoundations.Ch06.ProkhorovMetric
