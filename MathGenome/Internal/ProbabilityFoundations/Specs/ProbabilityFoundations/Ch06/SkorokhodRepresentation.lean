import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.WeakFramework
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.ContinuityPartitions

/-!
Independent specification of paper.tex 1905–1968. The only separability
assumption concerns a Borel set of full mass for the limiting law. In
particular neither completeness of the metric nor separability of the ambient
space or of the approximating laws is assumed. Source probability spaces carry
their specified sigma algebra, with no completeness requirement.
-/

open MeasureTheory Filter Topology Set TopologicalSpace

namespace Specs.ProbabilityFoundations.Ch06.SkorokhodRepresentation

universe u v
noncomputable section

/-- A realization on one probability space with one measurable full event. -/
def AlmostSureRepresentation {S : Type u} [MetricSpace S] [MeasurableSpace S]
    (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S) : Prop :=
  ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω),
    letI := mΩ
    ∃ (P : ProbabilityMeasure Ω) (X : Ω → S) (Xs : ℕ → Ω → S),
      Measurable X ∧ (∀ n, Measurable (Xs n)) ∧
      Measure.map X (P : Measure Ω) = (μ : Measure S) ∧
      (∀ n, Measure.map (Xs n) (P : Measure Ω) = (μs n : Measure S)) ∧
      ∃ E : Set Ω, MeasurableSet E ∧ (P : Measure Ω) E = 1 ∧
        ∀ ω ∈ E, Tendsto (fun n => Xs n ω) atTop (𝓝 (X ω))

/-- The optional modification keeps every variable unchanged on the common
full event and retains all its marginal laws, with convergence at every point. -/
def nullModificationType : Prop := ∀ {Ω : Type u} {S : Type v}
  [MeasurableSpace Ω] [MetricSpace S] [MeasurableSpace S]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (X : Ω → S) (Xs : ℕ → Ω → S),
  Measurable X → (∀ n, Measurable (Xs n)) →
  ∀ E : Set Ω, MeasurableSet E → P E = 1 →
  (∀ ω ∈ E, Tendsto (fun n => Xs n ω) atTop (𝓝 (X ω))) →
  ∃ Ys : ℕ → Ω → S,
    (∀ n, Measurable (Ys n)) ∧
    (∀ n ω, ω ∈ E → Ys n ω = Xs n ω) ∧
    (∀ n, Measure.map (Ys n) P = Measure.map (Xs n) P) ∧
    ∀ ω, Tendsto (fun n => Ys n ω) atTop (𝓝 (X ω))

def representationType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S]
  (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S),
  Tendsto μs atTop (𝓝 μ) →
  (∃ M : Set S, MeasurableSet M ∧ TopologicalSpace.IsSeparable M ∧ (μ : Measure S) M = 1) →
  AlmostSureRepresentation μs μ

/-- Separability of the whole space is sufficient; completeness is absent. -/
def separableRepresentationType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S] [SeparableSpace S]
  (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S),
  Tendsto μs atTop (𝓝 μ) → AlmostSureRepresentation μs μ

/-- A simultaneous realization converging everywhere. -/
def EverywhereRepresentation {S : Type u} [MetricSpace S] [MeasurableSpace S]
    (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S) : Prop :=
  ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω),
    letI := mΩ
    ∃ (P : ProbabilityMeasure Ω) (X : Ω → S) (Xs : ℕ → Ω → S),
      Measurable X ∧ (∀ n, Measurable (Xs n)) ∧
      Measure.map X (P : Measure Ω) = (μ : Measure S) ∧
      (∀ n, Measure.map (Xs n) (P : Measure Ω) = (μs n : Measure S)) ∧
      ∀ ω, Tendsto (fun n => Xs n ω) atTop (𝓝 (X ω))

def modificationOfRepresentationType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S),
  AlmostSureRepresentation μs μ → EverywhereRepresentation μs μ

/-- The optional everywhere-convergent version under the original hypotheses. -/
def everywhereRepresentationType : Prop := ∀ {S : Type u} [MetricSpace S]
  [MeasurableSpace S] [BorelSpace S]
  (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S),
  Tendsto μs atTop (𝓝 μ) →
  (∃ M : Set S, MeasurableSet M ∧ IsSeparable M ∧ (μ : Measure S) M = 1) →
  EverywhereRepresentation μs μ

end
end Specs.ProbabilityFoundations.Ch06.SkorokhodRepresentation
