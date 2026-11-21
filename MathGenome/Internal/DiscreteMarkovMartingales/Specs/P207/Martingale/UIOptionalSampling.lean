import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.TerminalStoppedRepresentation

/-! Independent statement of paper.tex §7.3, W41, Sampling a closed martingale.
The hypotheses are the source one-step martingale condition and uniform
integrability, with no boundedness or almost-sure finiteness imposed on either
stop. Both infinite layers use the fixed terminal representative from W34. -/

open MeasureTheory
open scoped MeasureTheory

universe u
namespace P207.UIOptionalSamplingSpec

/-- UI optional sampling, including equality of expectations with time zero. -/
def ui_optional_sampling : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ),
    IsMartingale M ℱ μ →
    Specs.P207.Martingale.UniformIntegrability.SourceUniformIntegrableValue μ M →
    ∀ (σ τ : Ω → WithTop ℕ)
      (hσ : IsDiscreteStoppingTime ℱ σ) (hτ : IsDiscreteStoppingTime ℱ τ),
      (∀ ω, σ ω ≤ τ ω) →
      Integrable (fullStoppedValue M σ (ℱ.limitProcess M μ)) μ ∧
      Integrable (fullStoppedValue M τ (ℱ.limitProcess M μ)) μ ∧
      μ[fullStoppedValue M τ (ℱ.limitProcess M μ) | stoppedSigma hσ] =ᵐ[μ]
        fullStoppedValue M σ (ℱ.limitProcess M μ) ∧
      (∫ ω, fullStoppedValue M τ (ℱ.limitProcess M μ) ω ∂μ) =
        (∫ ω, fullStoppedValue M σ (ℱ.limitProcess M μ) ω ∂μ) ∧
      (∫ ω, fullStoppedValue M σ (ℱ.limitProcess M μ) ω ∂μ) =
        ∫ ω, M 0 ω ∂μ

end P207.UIOptionalSamplingSpec
