import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.Stopping

open MeasureTheory
open scoped MeasureTheory

universe u
namespace P207.BoundedMartingaleSamplingSpec

/-- Bounded optional sampling for a real martingale (paper.tex, §7.2, W40).
The arbitrary supplied values at infinity are unused under the pointwise bound.
No positivity of the horizon or strict ordering of the stops is required. -/
def bounded_martingale_sampling : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ),
    IsMartingale M ℱ μ →
    ∀ (σ τ : Ω → WithTop ℕ)
      (hσ : IsDiscreteStoppingTime ℱ σ) (hτ : IsDiscreteStoppingTime ℱ τ)
      (N : ℕ),
      (∀ ω, σ ω ≤ τ ω) → (∀ ω, τ ω ≤ N) →
      ∀ (Yσ Yτ : Ω → ℝ),
        Integrable (fullStoppedValue M σ Yσ) μ ∧
        Integrable (fullStoppedValue M τ Yτ) μ ∧
        Measurable[stoppedSigma hσ] (fullStoppedValue M σ Yσ) ∧
        Measurable[stoppedSigma hτ] (fullStoppedValue M τ Yτ) ∧
        μ[fullStoppedValue M τ Yτ | stoppedSigma hσ] =ᵐ[μ]
          fullStoppedValue M σ Yσ ∧
        (∫ ω, fullStoppedValue M τ Yτ ω ∂μ) =
          ∫ ω, fullStoppedValue M σ Yσ ω ∂μ

end P207.BoundedMartingaleSamplingSpec
