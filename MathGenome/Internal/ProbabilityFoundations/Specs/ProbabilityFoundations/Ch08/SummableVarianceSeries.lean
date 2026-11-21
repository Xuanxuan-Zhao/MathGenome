import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.ProbabilityBounds
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Independent specification of paper.tex, Corollary 8.5, `cor:series-variance`.
The index `k : ℕ` labels the source variable X_{k+1}; `range n` therefore
represents exactly the first n terms in their original order. Summability is
assumed only for the nonnegative numerical variances. The sample series is
expressed by convergence of its ordered partial sums, with a single measurable
square-integrable limit for both modes. The probability space is not completed. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Specs.ProbabilityFoundations.Ch08.SummableVarianceSeries
universe u

noncomputable def summableVarianceSeriesType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ),
    (∀ k, Measurable (X k)) →
    Ch02.IndependenceInterfaces.IndependentRandomElementsValue P X →
    (∀ k, MemLp (X k) 2 P) →
    (∀ k, (∫ ω, X k ω ∂P) = 0) →
    Summable (fun k => Ch01.ProbabilityBounds.realVarianceValue P (X k)) →
    ∃ Z : Ω → ℝ, Measurable Z ∧ MemLp Z 2 P ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => ∑ k ∈ Finset.range n, X k ω) atTop (𝓝 (Z ω))) ∧
      Tendsto (fun n => ∫ ω, |(∑ k ∈ Finset.range n, X k ω) - Z ω| ^ 2 ∂P)
        atTop (𝓝 0)

end Specs.ProbabilityFoundations.Ch08.SummableVarianceSeries
