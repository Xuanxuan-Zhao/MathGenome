import Mathlib.MeasureTheory.Measure.Real

/-! Independent statements for paper.tex, Proposition p205:W15.
`μ.real A` is `(μ A).toReal`; probability measures are finite, so this
is the usual real probability. A finite index type also represents an
arbitrary finite set by taking its subtype, and may be empty. -/

open MeasureTheory

universe u v

namespace Specs.P205.Probability

/-- Finite subadditivity for measurable events in any probability space. -/
def UnionBound : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {I : Type v} [Fintype I] (A : I → Set Ω),
    (∀ i, MeasurableSet (A i)) → μ.real (⋃ i, A i) ≤ ∑ i, μ.real (A i)

/-- Quantitative lower bound on the probability of simultaneous avoidance. -/
def AvoidanceLowerBound : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {I : Type v} [Fintype I] (A : I → Set Ω),
    (∀ i, MeasurableSet (A i)) →
      1 - ∑ i, μ.real (A i) ≤ μ.real (⋂ i, (A i)ᶜ)

/-- The strict threshold gives positive probability of avoiding every event. -/
def PositiveAvoidance : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {I : Type v} [Fintype I] (A : I → Set Ω),
    (∀ i, MeasurableSet (A i)) →
      (∑ i, μ.real (A i)) < 1 → 0 < μ.real (⋂ i, (A i)ᶜ)

/-- The supplied notes' witness formulation of finite avoidance. -/
def ExistsAvoiding : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {I : Type v} [Fintype I] (A : I → Set Ω),
    (∀ i, MeasurableSet (A i)) →
      (∑ i, μ.real (A i)) < 1 → ∃ ω : Ω, ∀ i, ω ∉ A i

/-- In the empty family the bad union has probability zero and the good
intersection has probability one. No nonempty-index assumption is made. -/
def EmptyFamily : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {I : Type v} [Fintype I] [IsEmpty I] (A : I → Set Ω),
    μ.real (⋃ i, A i) = 0 ∧ μ.real (⋂ i, (A i)ᶜ) = 1

end Specs.P205.Probability
