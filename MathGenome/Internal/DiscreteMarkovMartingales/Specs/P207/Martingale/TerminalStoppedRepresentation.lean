import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.Stopping
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.UIMartingaleClosure

/-! Independent statements for the arbitrary-stop representation in paper.tex W41.
The stopped value uses the supplied terminal variable on the infinite layer.
No almost-sure finiteness or boundedness of the stopping time is required. -/

open MeasureTheory
open scoped MeasureTheory

universe u
namespace P207.TerminalStoppedRepresentationSpec

/-- Representation for any integrable terminal variable closing the process. -/
def closed_martingale_fullStoppedValue : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (Y : Ω → ℝ),
    Adapted ℱ M → Measurable[terminalSigma ℱ] Y → Integrable Y μ →
    (∀ n, M n =ᵐ[μ] μ[Y | ℱ n]) →
    ∀ (ρ : Ω → WithTop ℕ) (hρ : IsDiscreteStoppingTime ℱ ρ),
      Measurable[stoppedSigma hρ] (fullStoppedValue M ρ Y) ∧
      Integrable (fullStoppedValue M ρ Y) μ ∧
      (∫ ω, |fullStoppedValue M ρ Y ω| ∂μ) ≤ ∫ ω, |Y ω| ∂μ ∧
      fullStoppedValue M ρ Y =ᵐ[μ] μ[Y | stoppedSigma hρ]

/-- Specialization to the fixed terminal representative furnished by UI closure. -/
def ui_martingale_fullStoppedValue : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ),
    IsMartingale M ℱ μ →
    Specs.P207.Martingale.UniformIntegrability.SourceUniformIntegrableValue μ M →
    ∀ (ρ : Ω → WithTop ℕ) (hρ : IsDiscreteStoppingTime ℱ ρ),
      Measurable[stoppedSigma hρ] (fullStoppedValue M ρ (ℱ.limitProcess M μ)) ∧
      Integrable (fullStoppedValue M ρ (ℱ.limitProcess M μ)) μ ∧
      (∫ ω, |fullStoppedValue M ρ (ℱ.limitProcess M μ) ω| ∂μ) ≤
        ∫ ω, |ℱ.limitProcess M μ ω| ∂μ ∧
      fullStoppedValue M ρ (ℱ.limitProcess M μ) =ᵐ[μ]
        μ[ℱ.limitProcess M μ | stoppedSigma hρ]

end P207.TerminalStoppedRepresentationSpec
