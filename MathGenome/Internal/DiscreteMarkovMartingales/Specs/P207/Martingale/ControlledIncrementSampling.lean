import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.Stopping
import Mathlib.Basic.Real.ENatENNReal

open MeasureTheory
open scoped MeasureTheory
universe u
namespace P207.ControlledIncrementSamplingSpec

/-- Finite extended expectation uses the usual embedding of `ℕ ∪ {∞}` into
`[0,∞]`, so a positive mass at infinity is excluded by this hypothesis. -/
def controlled_increment_sampling : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ),
    IsMartingale M ℱ μ →
    ∀ (τ : Ω → WithTop ℕ), IsDiscreteStoppingTime ℱ τ →
    (∫⁻ ω, ENat.toENNReal (τ ω) ∂μ) < ⊤ →
    ∀ (C : ℝ), 0 ≤ C →
    (∀ k, μ[(fun ω => |M (k + 1) ω - M k ω|) | ℱ k] ≤ᵐ[μ] fun _ => C) →
    (∀ᵐ ω ∂μ, τ ω < ⊤) ∧
    Integrable (fullStoppedValue M τ (fun _ => 0)) μ ∧
    (∫ ω, fullStoppedValue M τ (fun _ => 0) ω ∂μ) = ∫ ω, M 0 ω ∂μ

/-- The pointwise almost-sure bounded-increment specialization. -/
def bounded_increment_sampling : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ),
    IsMartingale M ℱ μ →
    ∀ (τ : Ω → WithTop ℕ), IsDiscreteStoppingTime ℱ τ →
    (∫⁻ ω, ENat.toENNReal (τ ω) ∂μ) < ⊤ →
    ∀ (C : ℝ), 0 ≤ C →
    (∀ k, ∀ᵐ ω ∂μ, |M (k + 1) ω - M k ω| ≤ C) →
    (∀ᵐ ω ∂μ, τ ω < ⊤) ∧
    Integrable (fullStoppedValue M τ (fun _ => 0)) μ ∧
    (∫ ω, fullStoppedValue M τ (fun _ => 0) ω ∂μ) = ∫ ω, M 0 ω ∂μ

end P207.ControlledIncrementSamplingSpec
