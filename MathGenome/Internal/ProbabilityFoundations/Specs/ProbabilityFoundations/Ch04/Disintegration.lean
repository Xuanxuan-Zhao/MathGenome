import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.StandardBorel
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.KernelMeasure

/-!
Independent specification of `paper.tex`, §4.3, `thm:disintegration`.
The base has an arbitrary specified measurable structure. The target is nonempty
and standard Borel in the manuscript's sense. The product uses these specified
sigma-algebras. `IsMarkovKernel K` requires `K s` to be a probability measure for
every `s`, including points in any exceptional marginal-null set.
-/

open MeasureTheory ProbabilityTheory

namespace Specs.ProbabilityFoundations.Ch04.Disintegration

universe u v

/-- Disintegration with respect to any given first marginal. Its probability
normalization follows from that of the joint measure, so needs no extra hypothesis. -/
def disintegration_type : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T] [Nonempty T],
    _root_.ProbabilityFoundations.Ch04.Specs.StandardBorelValue T →
    ∀ (M : Measure (S × T)) [IsProbabilityMeasure M] (μ : Measure S),
      M.map Prod.fst = μ →
      ∃ K : Kernel S T, IsMarkovKernel K ∧
        M = KernelMeasure.kernelMeasureValue μ K

end Specs.ProbabilityFoundations.Ch04.Disintegration
