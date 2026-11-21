import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch04.DisintegrationUniqueness
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.StandardBorel
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.KernelMeasure
import Mathlib.Probability.Kernel.CompProdEqIff

/-! Simultaneous uniqueness of disintegrations over an arbitrary measurable base. -/

open MeasureTheory ProbabilityTheory

namespace ProbabilityFoundations.Ch04

universe u v

/-- Two disintegrations of the same joint probability agree as whole measures
outside one measurable null set in the original base sigma-algebra. -/
theorem disintegration_simultaneous_uniqueness
    {S : Type u} {T : Type v} [MeasurableSpace S] [MeasurableSpace T] [Nonempty T]
    (hT : IsStandardBorel T)
    (μ : Measure S) [IsProbabilityMeasure μ]
    (M : Measure (S × T)) [IsProbabilityMeasure M]
    (_hfst : M.map Prod.fst = μ)
    (K L : Kernel S T) [IsMarkovKernel K] [IsMarkovKernel L]
    (hK : M = kernelMeasure μ K) (hL : M = kernelMeasure μ L) :
    ∃ N : Set S, MeasurableSet N ∧ μ N = 0 ∧ ∀ s ∉ N, K s = L s := by
  let : StandardBorelSpace T := (isStandardBorel_iff T).mp hT
  have hprod : μ.compProd K = μ.compProd L := hK.symm.trans hL
  have hae : ∀ᵐ s ∂μ, K s = L s := Kernel.ae_eq_of_compProd_eq hprod
  obtain ⟨N, hsub, hN, hnull⟩ := exists_measurable_superset_of_null (ae_iff.mp hae)
  refine ⟨N, hN, hnull, ?_⟩
  intro s hs
  by_contra hne
  exact hs (hsub hne)

end ProbabilityFoundations.Ch04
