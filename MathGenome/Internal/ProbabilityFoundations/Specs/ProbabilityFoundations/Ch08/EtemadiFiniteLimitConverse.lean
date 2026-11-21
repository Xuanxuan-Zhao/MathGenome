import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch08.EtemadiStrongLaw

/-! Independent specification of the converse in Theorem 8.3,
`paper.tex:2796–2799, 2828–2837`. The source uses one-based partial
sums. The finite limit is an arbitrary measurable real random variable;
no integrability or constancy of this limit is assumed. -/

open MeasureTheory Filter
open scoped Topology

namespace Specs.ProbabilityFoundations.Ch08.EtemadiFiniteLimitConverse

universe u

def etemadiFiniteLimitConverseType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (_hX : ∀ k : ℕ, Measurable (X (k + 1)))
    (_hindep : Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces.PairwiseIndependentRandomElementsValue
      P (fun k : ℕ => X (k + 1)))
    (_hident : ∀ k : ℕ, ProbabilityTheory.IdentDistrib (X (k + 1)) (X 1) P P)
    (Z : Ω → ℝ) (_hZ : Measurable Z)
    (_hlim : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, X k ω) / (n : ℝ))
      atTop (𝓝 (Z ω))),
    Integrable (fun ω => |X 1 ω|) P ∧
      ∀ᵐ ω ∂P, Z ω = ∫ ω, X 1 ω ∂P

end Specs.ProbabilityFoundations.Ch08.EtemadiFiniteLimitConverse
