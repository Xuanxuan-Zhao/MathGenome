import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.ProbabilityBounds

/-! Independent specification of paper.tex, Theorem 8.4 (`thm:kolm-max`).
`Fin n` labels X₁,…,Xₙ by 0,…,n−1. The sum over indices `< k` is Sₖ.
The existence event is exactly the non-strict maximum crossing event.
The empty family is also allowed, giving the valid stronger n = 0 case.
No completion of the specified probability space is used. -/

open MeasureTheory
open scoped ENNReal

namespace Specs.ProbabilityFoundations.Ch08.KolmogorovMaximalInequality
universe u

noncomputable def kolmogorovMaximalType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ),
    (∀ i, Measurable (X i)) →
    Ch02.IndependenceInterfaces.IndependentRandomElementsValue P X →
    (∀ i, MemLp (X i) 2 P) →
    (∀ i, (∫ ω, X i ω ∂P) = 0) →
    ∀ (a : ℝ), 0 < a →
    P {ω | ∃ k ∈ Finset.Icc 1 n,
      a ≤ |∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), X i ω|} ≤
      ENNReal.ofReal ((∑ i, Ch01.ProbabilityBounds.realVarianceValue P (X i)) / a ^ 2)

end Specs.ProbabilityFoundations.Ch08.KolmogorovMaximalInequality
