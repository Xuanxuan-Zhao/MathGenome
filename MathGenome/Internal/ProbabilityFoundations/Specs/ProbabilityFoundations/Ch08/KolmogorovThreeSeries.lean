import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch08.ThreeSeriesVarianceNecessity

/-! Independent specification of Theorem 8.8, paper.tex:2926–2972.
Indices start at zero. The middle series uses ordered real partial sums,
so its convergence need not be absolute. The original variables have no
moment assumption, and the given probability space need not be complete. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Specs.ProbabilityFoundations.Ch08.KolmogorovThreeSeries

universe u
open _root_.ProbabilityFoundations.Ch08

noncomputable def kolmogorovThreeSeriesType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ), (∀ k, Measurable (X k)) →
    ProbabilityTheory.iIndepFun X P → ∀ a : ℝ, 0 < a →
    ((∀ᵐ ω ∂P, OrderedSeriesConverges (fun k => X k ω)) ↔
      (∑' k, P {ω | a < |X k ω|}) < ∞ ∧
      OrderedSeriesConverges (fun k => ∫ ω, symmetricTruncation a X k ω ∂P) ∧
      Summable (fun k => ProbabilityTheory.variance (symmetricTruncation a X k) P))

end Specs.ProbabilityFoundations.Ch08.KolmogorovThreeSeries
