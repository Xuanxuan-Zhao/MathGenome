import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.Portmanteau

/-! Converging together, paper.tex 1647–1678. The source spaces may vary
with both indices. Only the law of the first coordinate is fixed across m.
All probabilities of errors are extended nonnegative reals. -/
open MeasureTheory Filter Topology
open scoped ENNReal

namespace Specs.ProbabilityFoundations.Ch06.ConvergingTogether
universe u v
noncomputable section

def convergingTogetherType : Prop :=
  ∀ {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    {Ω : ℕ → ℕ → Type v} [∀ m n, MeasurableSpace (Ω m n)]
    (P : ∀ m n, Measure (Ω m n)) [∀ m n, IsProbabilityMeasure (P m n)]
    (X Y : ∀ m n, Ω m n → S)
    (hX : ∀ m n, Measurable (X m n)) (hY : ∀ m n, Measurable (Y m n))
    (ν : ℕ → ProbabilityMeasure S) (η : ℕ → ProbabilityMeasure S)
    (μ : ProbabilityMeasure S),
    (∀ m n, WeakFramework.probabilityLawValue (P m n) (X m n) (hX m n) = ν n) →
    (∀ m n, Measurable (fun ω => dist (X m n ω) (Y m n ω))) →
    (∀ m, Tendsto (fun n => WeakFramework.probabilityLawValue (P m n)
      (Y m n) (hY m n)) atTop (𝓝 (η m))) →
    Tendsto η atTop (𝓝 μ) →
    (∀ ε : ℝ, 0 < ε → Tendsto
      (fun m => limsup (fun n => P m n {ω | ε < dist (X m n ω) (Y m n ω)}) atTop)
      atTop (𝓝 0)) →
    Tendsto ν atTop (𝓝 μ)

def perturbationType : Prop :=
  ∀ {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    {Ω : ℕ → Type v} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Ω n → S)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (μ : ProbabilityMeasure S),
    (∀ n, Measurable (fun ω => dist (X n ω) (Y n ω))) →
    Tendsto (fun n => WeakFramework.probabilityLawValue (P n) (Y n) (hY n))
      atTop (𝓝 μ) →
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => P n {ω | ε < dist (X n ω) (Y n ω)})
      atTop (𝓝 0)) →
    Tendsto (fun n => WeakFramework.probabilityLawValue (P n) (X n) (hX n))
      atTop (𝓝 μ)

def measurableDistanceType : Prop :=
  ∀ {S : Type u} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace.SeparableSpace S] {Ω : Type v} [MeasurableSpace Ω]
    (X Y : Ω → S), Measurable X → Measurable Y →
    Measurable (fun ω => dist (X ω) (Y ω))

end
end Specs.ProbabilityFoundations.Ch06.ConvergingTogether
