import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter
open scoped Topology ENNReal

namespace ProbabilityFoundations.Ch01.Specs

universe u v

/-- Nonnegative integration is extended valued; no finiteness or completeness of μ. -/
def MonotoneConvergence : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α)
    (F : ℕ → α → ℝ≥0∞) (f : α → ℝ≥0∞),
    (∀ n, Measurable (F n)) → Measurable f →
    (∀ᵐ x ∂μ, Monotone (fun n => F n x)) →
    (∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) →
    Monotone (fun n => ∫⁻ x, F n x ∂μ) ∧
    Tendsto (fun n => ∫⁻ x, F n x ∂μ) atTop (𝓝 (∫⁻ x, f x ∂μ))

def Fatou : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α)
    (F : ℕ → α → ℝ≥0∞), (∀ n, Measurable (F n)) →
    ∫⁻ x, liminf (fun n => F n x) atTop ∂μ ≤
      liminf (fun n => ∫⁻ x, F n x ∂μ) atTop

/-- The norm formulation simultaneously covers real absolute value and complex modulus.
The codomain generality includes both ℝ and ℂ with their usual Borel structures. -/
def DominatedConvergence : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α)
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (F : ℕ → α → E) (f : α → E) (g : α → ℝ),
    (∀ n, Measurable (F n)) → Measurable f → Measurable g →
    (∀ᵐ x ∂μ, 0 ≤ g x) → Integrable g μ →
    (∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ g x) →
    (∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) →
    Integrable f μ ∧ (∀ n, Integrable (F n) μ) ∧
    Tendsto (fun n => ∫ x, ‖F n x - f x‖ ∂μ) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ))

/-- A common bound on a measurable finite-measure set, with a.e. vanishing outside it.
No bound on the measure of the whole space is imposed. -/
def BoundedConvergence : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α)
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (F : ℕ → α → E) (f : α → E) (s : Set α) (C : ℝ),
    MeasurableSet s → μ s < ∞ → 0 ≤ C →
    (∀ n, Measurable (F n)) → Measurable f →
    (∀ n, ∀ᵐ x ∂μ, x ∈ s → ‖F n x‖ ≤ C) →
    (∀ n, ∀ᵐ x ∂μ, x ∉ s → F n x = 0) →
    (∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) →
    Integrable f μ ∧ (∀ n, Integrable (F n) μ) ∧
    Tendsto (fun n => ∫ x, ‖F n x - f x‖ ∂μ) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ))

end ProbabilityFoundations.Ch01.Specs
