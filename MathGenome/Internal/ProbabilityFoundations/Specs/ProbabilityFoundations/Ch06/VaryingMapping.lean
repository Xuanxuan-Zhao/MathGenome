import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.WeakFramework
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Independent statements for paper.tex, Theorem `thm:p06-mapping` (1592–1621).
Both spaces carry exactly their Borel sigma algebras. No separability or
completeness is assumed. Continuity in the corollary is in the entire domain. -/

open MeasureTheory Filter Topology Set

namespace Specs.ProbabilityFoundations.Ch06.VaryingMapping

universe u v

noncomputable section

def varyingMappingType : Prop :=
  ∀ {S : Type u} {T : Type v} [MetricSpace S] [MetricSpace T]
    [MeasurableSpace S] [BorelSpace S] [MeasurableSpace T] [BorelSpace T]
    (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S)
    (gs : ℕ → S → T) (g : S → T),
    (∀ n, Measurable (gs n)) → Measurable g →
    Tendsto μs atTop (𝓝 μ) →
    ∀ C : Set S, MeasurableSet C → (μ : Measure S) C = 1 →
    (∀ x ∈ C, ∀ xs : ℕ → S, Tendsto xs atTop (𝓝 x) →
      Tendsto (fun n => gs n (xs n)) atTop (𝓝 (g x))) →
    Tendsto (fun n => (μs n).map (gs n)) atTop (𝓝 (μ.map g))

def almostEverywhereContinuousMappingType : Prop :=
  ∀ {S : Type u} {T : Type v} [MetricSpace S] [MetricSpace T]
    [MeasurableSpace S] [BorelSpace S] [MeasurableSpace T] [BorelSpace T]
    (μs : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S)
    (g : S → T), Measurable g → Tendsto μs atTop (𝓝 μ) →
    (∀ᵐ x ∂(μ : Measure S), ContinuousAt g x) →
    Tendsto (fun n => (μs n).map g) atTop (𝓝 (μ.map g))

end
end Specs.ProbabilityFoundations.Ch06.VaryingMapping
