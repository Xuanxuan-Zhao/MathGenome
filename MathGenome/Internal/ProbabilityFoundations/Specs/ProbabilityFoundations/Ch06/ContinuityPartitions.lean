import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Topology.MetricSpace.Bounded

/-! Independent statements for paper.tex 1464–1471 and 1516–1533.
The finite partition is represented by a distinguished remainder and a finite
set of nonempty other cells. Boundedness is explicit because `Metric.diam`
alone uses the value zero for unbounded sets. -/

open MeasureTheory TopologicalSpace Metric Set

namespace Specs.ProbabilityFoundations.Ch06.ContinuityPartitions

universe u
noncomputable section

def isContinuitySetType := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S], Measure S → Set S → Prop

def isContinuitySetValue : isContinuitySetType := fun μ A =>
  MeasurableSet A ∧ μ (frontier A) = 0

def countableBadBallRadiiType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsFiniteMeasure μ] (x : S),
  {t : ℝ | 0 < t ∧ ¬ isContinuitySetValue μ (ball x t)}.Countable

def smallContinuityPartitionType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
  (M : Set S), MeasurableSet M → IsSeparable M → μ M = 1 →
  ∀ (r ε : ℝ), 0 < r → 0 < ε →
  ∃ (A₀ : Set S) (C : Finset (Set S)),
    isContinuitySetValue μ A₀ ∧ μ A₀ < ENNReal.ofReal ε ∧
    (C : Set (Set S)).Pairwise Disjoint ∧
    (∀ A ∈ C, A.Nonempty ∧ isContinuitySetValue μ A ∧
      Bornology.IsBounded A ∧ diam A < r) ∧
    (∀ A ∈ C, Disjoint A₀ A) ∧
    A₀ ∪ (⋃ A ∈ C, A) = univ

end
end Specs.ProbabilityFoundations.Ch06.ContinuityPartitions
