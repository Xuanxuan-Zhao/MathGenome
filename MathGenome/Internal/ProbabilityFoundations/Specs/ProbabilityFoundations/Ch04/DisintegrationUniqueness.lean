import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.StandardBorel
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.KernelMeasure

/-!
Independent statement of the simultaneous uniqueness assertion of
`paper.tex`, Theorem `thm:kernel-conditional-integration` (§4.4).
The hypotheses on the joint law are those of Theorem `thm:disintegration`:
the base has an arbitrary specified sigma-algebra and the target is a nonempty
standard Borel space. The exceptional set belongs to the original sigma-algebra;
no completion is used. Outside that single set, the entire measures agree.
-/

open MeasureTheory ProbabilityTheory

namespace Specs.ProbabilityFoundations.Ch04.DisintegrationUniqueness

universe u v

def simultaneous_uniqueness_type : Prop :=
  ∀ {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T] [Nonempty T],
    _root_.ProbabilityFoundations.Ch04.Specs.StandardBorelValue T →
    ∀ (μ : Measure S) [IsProbabilityMeasure μ]
      (M : Measure (S × T)) [IsProbabilityMeasure M],
      M.map Prod.fst = μ →
      ∀ (K L : Kernel S T) [IsMarkovKernel K] [IsMarkovKernel L],
        M = KernelMeasure.kernelMeasureValue μ K →
        M = KernelMeasure.kernelMeasureValue μ L →
        ∃ N : Set S, MeasurableSet N ∧ μ N = 0 ∧ ∀ s ∉ N, K s = L s

end Specs.ProbabilityFoundations.Ch04.DisintegrationUniqueness
