import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.ProbabilityBounds
import Mathlib.Topology.Algebra.InfiniteSum.Real

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Specs.ProbabilityFoundations.Ch08.KolmogorovVarianceCriterion
universe u

/-! Corollary 8.7 of paper.tex. `X k` denotes the source variable X_{k+1};
`b n` is the source weight b_n. Thus the first n centered variables are
summed over `range n`, and their weights are `b (k + 1)`. The unused value
`b 0` has no positivity or monotonicity requirement. -/
noncomputable def varianceCriterionType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (b : ℕ → ℝ),
    (∀ k, Measurable (X k)) →
    Ch02.IndependenceInterfaces.IndependentRandomElementsValue P X →
    (∀ k, MemLp (X k) 2 P) →
    (∀ n, 1 ≤ n → 0 < b n) →
    MonotoneOn b (Set.Ici 1) →
    Tendsto b atTop atTop →
    Summable (fun k => Ch01.ProbabilityBounds.realVarianceValue P (X k) / b (k + 1) ^ 2) →
    ∀ᵐ ω ∂P, Tendsto
      (fun n => (b n)⁻¹ * ∑ k ∈ Finset.range n, (X k ω - ∫ t, X k t ∂P))
      atTop (𝓝 0)

/-- The specialization b_n = n, with E S_n written as the integral of S_n. -/
noncomputable def normalizedVarianceStrongLawType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ),
    (∀ k, Measurable (X k)) →
    Ch02.IndependenceInterfaces.IndependentRandomElementsValue P X →
    (∀ k, MemLp (X k) 2 P) →
    Summable (fun k => Ch01.ProbabilityBounds.realVarianceValue P (X k) / ((k + 1 : ℕ) : ℝ) ^ 2) →
    ∀ᵐ ω ∂P, Tendsto
      (fun n => ((∑ k ∈ Finset.range n, X k ω) -
        ∫ t, ∑ k ∈ Finset.range n, X k t ∂P) / (n : ℝ))
      atTop (𝓝 0)

end Specs.ProbabilityFoundations.Ch08.KolmogorovVarianceCriterion
