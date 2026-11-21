import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.MomentIdentities

/-!
Independent specifications for the probabilistic assertions of Proposition
p205:W20, paper.tex 941–969. Probabilities are `μ.real A`, the real value of
`μ A`. Indicators are real-valued. No independence is imposed on a family.
A finite linear order describes any enumeration; neither it nor the index
family is required to be nonempty.
-/

open MeasureTheory
open scoped BigOperators

universe u v

namespace Specs.P205.Probability.IndicatorMoments

def IndicatorMemLp : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A : Set Ω}, MeasurableSet A → MemLp (A.indicator (fun _ ↦ (1 : ℝ))) 2 μ

def CountMemLp : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type v} [Fintype ι] {A : ι → Set Ω}, (∀ i, MeasurableSet (A i)) →
    MemLp (fun ω ↦ ∑ i, (A i).indicator (fun _ ↦ (1 : ℝ)) ω) 2 μ

def ExpectationCount : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type v} [Fintype ι] {A : ι → Set Ω}, (∀ i, MeasurableSet (A i)) →
    (∫ ω, ∑ i, (A i).indicator (fun _ ↦ (1 : ℝ)) ω ∂μ) = ∑ i, μ.real (A i)

def CovarianceIndicator : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A B : Set Ω}, MeasurableSet A → MeasurableSet B →
    ProbabilityTheory.covariance (A.indicator (fun _ ↦ (1 : ℝ)))
      (B.indicator (fun _ ↦ (1 : ℝ))) μ = μ.real (A ∩ B) - μ.real A * μ.real B

def VarianceIndicator : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A : Set Ω}, MeasurableSet A →
    ProbabilityTheory.variance (A.indicator (fun _ ↦ (1 : ℝ))) μ =
      μ.real A * (1 - μ.real A)

def VarianceCountCovariance : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type v} [Fintype ι] {A : ι → Set Ω}, (∀ i, MeasurableSet (A i)) →
    ProbabilityTheory.variance (fun ω ↦ ∑ i, (A i).indicator (fun _ ↦ (1 : ℝ)) ω) μ =
      ∑ i, ∑ j, ProbabilityTheory.covariance ((A i).indicator (fun _ ↦ (1 : ℝ)))
        ((A j).indicator (fun _ ↦ (1 : ℝ))) μ

def VarianceCountOrdered : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type v} [Fintype ι] [LinearOrder ι] {A : ι → Set Ω},
    (∀ i, MeasurableSet (A i)) →
    ProbabilityTheory.variance (fun ω ↦ ∑ i, (A i).indicator (fun _ ↦ (1 : ℝ)) ω) μ =
      (∑ i, μ.real (A i) * (1 - μ.real (A i))) +
        2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j ↦ i < j),
          (μ.real (A i ∩ A j) - μ.real (A i) * μ.real (A j))

/-- The same conclusion using any explicit enumeration of the original family. -/
def VarianceCountEnumerated : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type v} [Fintype ι] {A : ι → Set Ω}, (∀ i, MeasurableSet (A i)) →
    ∀ {n : ℕ} (e : Fin n ≃ ι),
    ProbabilityTheory.variance (fun ω ↦ ∑ i, (A i).indicator (fun _ ↦ (1 : ℝ)) ω) μ =
      (∑ i : Fin n, μ.real (A (e i)) * (1 - μ.real (A (e i)))) +
        2 * ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j ↦ i < j),
          (μ.real (A (e i) ∩ A (e j)) - μ.real (A (e i)) * μ.real (A (e j)))

def IndependentCovariance : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A B : Set Ω}, MeasurableSet A → MeasurableSet B →
    ProbabilityTheory.IndepSet A B μ →
    ProbabilityTheory.covariance (A.indicator (fun _ ↦ (1 : ℝ)))
      (B.indicator (fun _ ↦ (1 : ℝ))) μ = 0

end Specs.P205.Probability.IndicatorMoments
