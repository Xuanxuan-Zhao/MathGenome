import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.VaryingMapping
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.KernelComposition
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! Independent statement of `cor:p06-mixtures`, paper.tex 1623–1645.
The mixture is the composition of the given probability measure with the given
Markov kernel. Both metric spaces have exactly their Borel sigma algebras.
There are no separability, tightness, or continuity assumptions outside `C`. -/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Specs.ProbabilityFoundations.Ch06.WeakMixtures

universe u v
noncomputable section

def mixedLawType := ∀ {S : Type u} {T : Type v}
  [MeasurableSpace S] [MeasurableSpace T],
  ProbabilityMeasure S → (K : Kernel S T) → [IsMarkovKernel K] → ProbabilityMeasure T

def mixedLawValue : mixedLawType := fun μ K _ => ⟨K ∘ₘ (μ : Measure _), inferInstance⟩

def weakMixturesType : Prop :=
  ∀ {S : Type u} {T : Type v} [MetricSpace S] [MetricSpace T]
    [MeasurableSpace S] [BorelSpace S] [MeasurableSpace T] [BorelSpace T]
    (ηs : ℕ → ProbabilityMeasure S) (η : ProbabilityMeasure S)
    (Ks : ℕ → Kernel S T) (K : Kernel S T)
    [∀ n, IsMarkovKernel (Ks n)] [IsMarkovKernel K],
    Tendsto ηs atTop (𝓝 η) →
    ∀ C : Set S, MeasurableSet C → (η : Measure S) C = 1 →
    (∀ x ∈ C, ∀ xs : ℕ → S, Tendsto xs atTop (𝓝 x) →
      Tendsto (fun n => (⟨Ks n (xs n), inferInstance⟩ : ProbabilityMeasure T)) atTop
        (nhds (X := ProbabilityMeasure T) ⟨K x, inferInstance⟩)) →
    Tendsto (fun n => mixedLawValue (ηs n) (Ks n)) atTop (𝓝 (mixedLawValue η K))

end
end Specs.ProbabilityFoundations.Ch06.WeakMixtures
