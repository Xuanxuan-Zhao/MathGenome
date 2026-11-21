import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.ProcessInterfaces
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.UniformIntegrability
import Mathlib.Probability.Process.LimitProcess

/-! Independent statements for paper.tex §6.5, W34, martingale assertions.
The fixed representative is Mathlib's `Filtration.limitProcess`; its sigma
algebra is the literal supremum of the finite-time sigma algebras. No
completeness of the probability space, terminal variable, or closure
certificate is assumed. The converse and submartingale assertions are
allocated to the separate fixed-input UI and submartingale closure goals. -/

open MeasureTheory Filter
open scoped MeasureTheory Topology

universe u
namespace P207.UIMartingaleClosureSpec

/-- All terminal conclusions for one fixed choice, usable downstream. -/
def terminal : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ),
    IsMartingale M ℱ μ →
    Specs.P207.Martingale.UniformIntegrability.SourceUniformIntegrableValue μ M →
    Measurable[terminalSigma ℱ] (ℱ.limitProcess M μ) ∧
      Integrable (ℱ.limitProcess M μ) μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n => M n ω) atTop (𝓝 (ℱ.limitProcess M μ ω))) ∧
      Tendsto (fun n => ∫ ω, ‖M n ω - ℱ.limitProcess M μ ω‖ ∂μ) atTop (𝓝 0) ∧
      ∀ n, M n =ᵐ[μ] μ[ℱ.limitProcess M μ | ℱ n]

/-- Source existential statement, with the full terminal representation. -/
def exists_terminal : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ),
    IsMartingale M ℱ μ →
    Specs.P207.Martingale.UniformIntegrability.SourceUniformIntegrableValue μ M →
    ∃ Y : Ω → ℝ, Measurable[terminalSigma ℱ] Y ∧ Integrable Y μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n => M n ω) atTop (𝓝 (Y ω))) ∧
      Tendsto (fun n => ∫ ω, ‖M n ω - Y ω‖ ∂μ) atTop (𝓝 0) ∧
      ∀ n, M n =ᵐ[μ] μ[Y | ℱ n]

/-- Any other almost-sure limit agrees with the fixed choice. -/
def terminal_unique : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ),
    IsMartingale M ℱ μ →
    Specs.P207.Martingale.UniformIntegrability.SourceUniformIntegrableValue μ M →
    ∀ Y : Ω → ℝ,
    (∀ᵐ ω ∂μ, Tendsto (fun n => M n ω) atTop (𝓝 (Y ω))) →
    Y =ᵐ[μ] ℱ.limitProcess M μ

end P207.UIMartingaleClosureSpec
