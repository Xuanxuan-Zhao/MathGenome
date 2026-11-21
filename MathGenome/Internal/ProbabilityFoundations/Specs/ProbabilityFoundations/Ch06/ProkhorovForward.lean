import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.Tightness

/-! Independent scope of the forward Prokhorov theorem, paper.tex 1785–1857.
The canonical topology is the weak topology of bounded continuous real tests
(identified in the upstream WeakFramework). No countability, completeness or
nonemptiness hypothesis is imposed on the metric space or on the family. -/

open MeasureTheory Filter Topology

namespace Specs.ProbabilityFoundations.Ch06.ProkhorovForward

universe u

def compactClosureType : Prop :=
  ∀ {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    (A : Set (ProbabilityMeasure S)), Tightness.uniformlyTightValue A →
    IsCompact (closure A)

def subsequenceType : Prop :=
  ∀ {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    (A : Set (ProbabilityMeasure S)), Tightness.uniformlyTightValue A →
    ∀ μ : ℕ → ProbabilityMeasure S, (∀ n, μ n ∈ A) →
      ∃ (ν : ProbabilityMeasure S) (φ : ℕ → ℕ), StrictMono φ ∧
        WeakFramework.weaklyConvergesValue atTop (μ ∘ φ) ν

end Specs.ProbabilityFoundations.Ch06.ProkhorovForward
