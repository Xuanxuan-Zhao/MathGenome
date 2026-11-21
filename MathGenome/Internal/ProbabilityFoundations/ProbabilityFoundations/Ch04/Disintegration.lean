import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.StandardBorel
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.KernelMeasure

/-!
Disintegration over an arbitrary measurable base (`paper.tex`, §4.3).
Only the target has a standard Borel hypothesis. Mathlib's conditional kernel of
a finite measure is a Markov kernel at every base point and disintegrates the
measure relative to its first marginal.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityFoundations.Ch04

universe u v

/-- Every joint probability with nonempty standard Borel target admits a
probability kernel relative to its specified first marginal. -/
theorem disintegration {S : Type u} {T : Type v}
    [MeasurableSpace S] [MeasurableSpace T] [Nonempty T]
    (hT : IsStandardBorel T) (M : Measure (S × T)) [IsProbabilityMeasure M]
    (μ : Measure S) (hμ : M.map Prod.fst = μ) :
    ∃ K : Kernel S T, IsMarkovKernel K ∧ M = kernelMeasure μ K := by
  let : StandardBorelSpace T := (isStandardBorel_iff T).mp hT
  refine ⟨M.condKernel, inferInstance, ?_⟩
  change M = μ.compProd M.condKernel
  have hfst : M.fst = μ := hμ
  rw [← hfst]
  exact (M.disintegrate M.condKernel).symm

end ProbabilityFoundations.Ch04
