import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.TerminalStoppedRepresentation
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.UIOptionalSampling

open MeasureTheory
open scoped MeasureTheory

universe u
namespace P207

variable {Ω : Type u} [m : MeasurableSpace Ω]

/-- Unbounded optional sampling for a source-UI real martingale. At each infinite
stop the value is the fixed terminal limit, even on a nonnull infinite layer. -/
theorem ui_optional_sampling (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ)
    (hM : IsMartingale M ℱ μ) (hui : Martingale.SourceUniformIntegrable μ M)
    (σ τ : Ω → WithTop ℕ)
    (hσ : IsDiscreteStoppingTime ℱ σ) (hτ : IsDiscreteStoppingTime ℱ τ)
    (hle : ∀ ω, σ ω ≤ τ ω) :
    Integrable (fullStoppedValue M σ (ℱ.limitProcess M μ)) μ ∧
      Integrable (fullStoppedValue M τ (ℱ.limitProcess M μ)) μ ∧
      μ[fullStoppedValue M τ (ℱ.limitProcess M μ) | stoppedSigma hσ] =ᵐ[μ]
        fullStoppedValue M σ (ℱ.limitProcess M μ) ∧
      (∫ ω, fullStoppedValue M τ (ℱ.limitProcess M μ) ω ∂μ) =
        (∫ ω, fullStoppedValue M σ (ℱ.limitProcess M μ) ω ∂μ) ∧
      (∫ ω, fullStoppedValue M σ (ℱ.limitProcess M μ) ω ∂μ) =
        ∫ ω, M 0 ω ∂μ := by
  obtain ⟨_, hiσ, _, hrσ⟩ := ui_martingale_fullStoppedValue μ ℱ M hM hui σ hσ
  obtain ⟨_, hiτ, _, hrτ⟩ := ui_martingale_fullStoppedValue μ ℱ M hM hui τ hτ
  have hσle : stoppedSigma hσ ≤ m :=
    (stoppedSigma_le_terminal hσ).trans (iSup_le ℱ.le)
  have hτle : stoppedSigma hτ ≤ m :=
    (stoppedSigma_le_terminal hτ).trans (iSup_le ℱ.le)
  have hsample :
      μ[fullStoppedValue M τ (ℱ.limitProcess M μ) | stoppedSigma hσ] =ᵐ[μ]
        fullStoppedValue M σ (ℱ.limitProcess M μ) :=
    (condExp_congr_ae hrτ).trans
      ((condExp_condExp_of_le (stoppedSigma_mono hσ hτ hle) hτle).trans hrσ.symm)
  refine ⟨hiσ, hiτ, hsample, ?_, ?_⟩
  · calc
      (∫ ω, fullStoppedValue M τ (ℱ.limitProcess M μ) ω ∂μ) =
          ∫ ω, μ[fullStoppedValue M τ (ℱ.limitProcess M μ) | stoppedSigma hσ] ω ∂μ :=
        (integral_condExp hσle).symm
      _ = ∫ ω, fullStoppedValue M σ (ℱ.limitProcess M μ) ω ∂μ :=
        integral_congr_ae hsample
  · calc
      (∫ ω, fullStoppedValue M σ (ℱ.limitProcess M μ) ω ∂μ) =
          ∫ ω, μ[ℱ.limitProcess M μ | stoppedSigma hσ] ω ∂μ :=
        integral_congr_ae hrσ
      _ = ∫ ω, ℱ.limitProcess M μ ω ∂μ := integral_condExp hσle
      _ = ∫ ω, μ[ℱ.limitProcess M μ | ℱ 0] ω ∂μ :=
        (integral_condExp (ℱ.le 0)).symm
      _ = ∫ ω, M 0 ω ∂μ :=
        integral_congr_ae ((ui_martingale_terminal μ ℱ M hM hui).2.2.2.2 0).symm

end P207
