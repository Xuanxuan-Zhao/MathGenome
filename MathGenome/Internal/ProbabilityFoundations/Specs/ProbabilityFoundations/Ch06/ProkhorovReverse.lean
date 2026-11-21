import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.Tightness

/-! Independent specification of paper.tex, lines 1859–1903. The space is
complete separable metric with its specified Borel sigma algebra. The sequence
condition permits limits anywhere in the space of probability laws, and does
not require them to belong to the original family. No nonemptiness hypothesis
is placed on the space or family. -/

open MeasureTheory Filter Topology TopologicalSpace

namespace Specs.ProbabilityFoundations.Ch06.ProkhorovReverse

universe u

/-- Reverse Prokhorov under the subsequence condition. -/
def subsequenceType : Prop :=
  ∀ {S : Type u} [MetricSpace S] [CompleteSpace S] [SeparableSpace S]
    [MeasurableSpace S] [BorelSpace S] (A : Set (ProbabilityMeasure S)),
    (∀ μ : ℕ → ProbabilityMeasure S, (∀ n, μ n ∈ A) →
      ∃ (ν : ProbabilityMeasure S) (φ : ℕ → ℕ), StrictMono φ ∧
        WeakFramework.weaklyConvergesValue atTop (μ ∘ φ) ν) →
    Tightness.uniformlyTightValue A

/-- Reverse Prokhorov under compactness of the weak closure. -/
def compactClosureType : Prop :=
  ∀ {S : Type u} [MetricSpace S] [CompleteSpace S] [SeparableSpace S]
    [MeasurableSpace S] [BorelSpace S] (A : Set (ProbabilityMeasure S)),
    IsCompact (closure A) → Tightness.uniformlyTightValue A

/-- Uniform tightness is equivalent to the subsequence condition. -/
def tightIffSubsequenceType : Prop :=
  ∀ {S : Type u} [MetricSpace S] [CompleteSpace S] [SeparableSpace S]
    [MeasurableSpace S] [BorelSpace S] (A : Set (ProbabilityMeasure S)),
    Tightness.uniformlyTightValue A ↔
      ∀ μ : ℕ → ProbabilityMeasure S, (∀ n, μ n ∈ A) →
        ∃ (ν : ProbabilityMeasure S) (φ : ℕ → ℕ), StrictMono φ ∧
          WeakFramework.weaklyConvergesValue atTop (μ ∘ φ) ν

/-- Uniform tightness is equivalent to compact weak closure. -/
def tightIffCompactClosureType : Prop :=
  ∀ {S : Type u} [MetricSpace S] [CompleteSpace S] [SeparableSpace S]
    [MeasurableSpace S] [BorelSpace S] (A : Set (ProbabilityMeasure S)),
    Tightness.uniformlyTightValue A ↔ IsCompact (closure A)

/-- The two compactness conditions are equivalent. -/
def compactClosureIffSubsequenceType : Prop :=
  ∀ {S : Type u} [MetricSpace S] [CompleteSpace S] [SeparableSpace S]
    [MeasurableSpace S] [BorelSpace S] (A : Set (ProbabilityMeasure S)),
    IsCompact (closure A) ↔
      ∀ μ : ℕ → ProbabilityMeasure S, (∀ n, μ n ∈ A) →
        ∃ (ν : ProbabilityMeasure S) (φ : ℕ → ℕ), StrictMono φ ∧
          WeakFramework.weaklyConvergesValue atTop (μ ∘ φ) ν

/-- Every individual Borel probability law on a complete separable metric
space is tight. -/
def probabilityTightType : Prop :=
  ∀ {S : Type u} [MetricSpace S] [CompleteSpace S] [SeparableSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ : ProbabilityMeasure S),
    Tightness.tightValue μ

end Specs.ProbabilityFoundations.Ch06.ProkhorovReverse
