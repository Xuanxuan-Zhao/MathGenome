import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.Stopping

open MeasureTheory
open scoped MeasureTheory

universe u
namespace P207.BoundedSubmartingaleSamplingSpec

/-- Bounded optional sampling, including measurability, integrability, the
conditional inequality and its expectation consequence. The supplied values on
infinite layers are arbitrary: the pointwise bound makes those layers empty. -/
def bounded_submartingale_sampling : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ),
    IsSubmartingale X ℱ μ →
    ∀ (σ τ : Ω → WithTop ℕ)
      (hσ : IsDiscreteStoppingTime ℱ σ) (hτ : IsDiscreteStoppingTime ℱ τ)
      (N : ℕ),
      (∀ ω, σ ω ≤ τ ω) → (∀ ω, τ ω ≤ N) →
      ∀ (Yσ Yτ : Ω → ℝ),
        Integrable (fullStoppedValue X σ Yσ) μ ∧
        Integrable (fullStoppedValue X τ Yτ) μ ∧
        Measurable[stoppedSigma hσ] (fullStoppedValue X σ Yσ) ∧
        Measurable[stoppedSigma hτ] (fullStoppedValue X τ Yτ) ∧
        fullStoppedValue X σ Yσ ≤ᵐ[μ]
          μ[fullStoppedValue X τ Yτ | stoppedSigma hσ] ∧
        (∫ ω, fullStoppedValue X σ Yσ ω ∂μ) ≤
          ∫ ω, fullStoppedValue X τ Yτ ω ∂μ

end P207.BoundedSubmartingaleSamplingSpec
