import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.WeakMetrics

/-!
The separable converse in paper.tex, Theorem 6.18, lines 2052–2117.
Each original real-valued distance is the distance of a metric whose topology
is exactly the initial topology of all bounded continuous real integral tests.
Equality of topologies includes continuity in both directions and arbitrary nets.
The state space is separable, with no completeness or compact support assumption.
-/

open MeasureTheory TopologicalSpace

namespace Specs.ProbabilityFoundations.Ch06.SeparableWeakMetrization

universe u
noncomputable section

def prokhorovMetrizesWeakType : Prop :=
  ∀ {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S] [SeparableSpace S],
    ∃ m : MetricSpace (ProbabilityMeasure S),
      (∀ μ ν, @dist _ m.toDist μ ν = WeakMetrics.prokhorovDistValue μ ν) ∧
      m.toUniformSpace.toTopologicalSpace = WeakFramework.weakTopologyValue (S := S)

def boundedLipschitzMetrizesWeakType : Prop :=
  ∀ {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S] [SeparableSpace S],
    ∃ m : MetricSpace (ProbabilityMeasure S),
      (∀ μ ν, @dist _ m.toDist μ ν = WeakMetrics.boundedLipschitzDistValue μ ν) ∧
      m.toUniformSpace.toTopologicalSpace = WeakFramework.weakTopologyValue (S := S)

end
end Specs.ProbabilityFoundations.Ch06.SeparableWeakMetrization
