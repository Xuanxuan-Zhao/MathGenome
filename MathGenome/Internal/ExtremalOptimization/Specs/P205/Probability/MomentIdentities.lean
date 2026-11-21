import Mathlib.Probability.Moments.Variance

/-!
Independent specifications for paper.tex, chapter "Moments and Concentration",
first section, the paragraph defining variance and covariance (lines 925–939).
The measure is an arbitrary probability measure and `MemLp X 2 μ` expresses
both almost-everywhere measurability and a finite second moment.
-/

open MeasureTheory

universe u

namespace Specs.P205.Probability.MomentIdentities

/-- The mean exists as a genuine integrable first moment. -/
def FirstMomentIntegrable : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ}, MemLp X 2 μ → Integrable X μ

/-- The square is integrable, rather than merely having a real-valued integral notation. -/
def SquareIntegrable : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ}, MemLp X 2 μ → Integrable (fun ω ↦ X ω ^ 2) μ

/-- Centering preserves the finite second moment. -/
def CenteredMemLp : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ}, MemLp X 2 μ →
      MemLp (fun ω ↦ X ω - ∫ x, X x ∂μ) 2 μ

/-- The uncentered product has a finite absolute integral. -/
def ProductIntegrable : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ}, MemLp X 2 μ → MemLp Y 2 μ →
      Integrable (fun ω ↦ X ω * Y ω) μ

/-- The squared deviation in the variance definition is integrable. -/
def CenteredSquareIntegrable : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ}, MemLp X 2 μ →
      Integrable (fun ω ↦ (X ω - ∫ x, X x ∂μ) ^ 2) μ

/-- The product in the covariance definition is integrable. -/
def CenteredProductIntegrable : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ}, MemLp X 2 μ → MemLp Y 2 μ →
      Integrable (fun ω ↦ (X ω - ∫ x, X x ∂μ) * (Y ω - ∫ x, Y x ∂μ)) μ

/-- Identification with the canonical Mathlib variance. -/
def VarianceEqCentered : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ}, MemLp X 2 μ →
      ProbabilityTheory.variance X μ = ∫ ω, (X ω - ∫ x, X x ∂μ) ^ 2 ∂μ

/-- Identification with the canonical Mathlib covariance. -/
def CovarianceEqCentered : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ}, MemLp X 2 μ → MemLp Y 2 μ →
      ProbabilityTheory.covariance X Y μ =
        ∫ ω, (X ω - ∫ x, X x ∂μ) * (Y ω - ∫ x, Y x ∂μ) ∂μ

/-- The expanded second-moment formula for variance. -/
def VarianceEqSecondMoment : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ}, MemLp X 2 μ →
      ProbabilityTheory.variance X μ = (∫ ω, X ω ^ 2 ∂μ) - (∫ ω, X ω ∂μ) ^ 2

/-- The expanded product-moment formula for covariance. -/
def CovarianceEqProductMoment : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ}, MemLp X 2 μ → MemLp Y 2 μ →
      ProbabilityTheory.covariance X Y μ =
        (∫ ω, X ω * Y ω ∂μ) - (∫ ω, X ω ∂μ) * (∫ ω, Y ω ∂μ)

end Specs.P205.Probability.MomentIdentities
