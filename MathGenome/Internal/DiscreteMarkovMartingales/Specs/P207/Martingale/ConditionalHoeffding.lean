import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.ProcessInterfaces

open MeasureTheory
open scoped MeasureTheory

universe u
namespace P207.ConditionalHoeffdingSpec

/-- The actual martingale increment has zero conditional mean. -/
def increment_condExp_zero : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ),
    P207.IsMartingale M ℱ μ → ∀ k,
      μ[(fun ω => M (k + 1) ω - M k ω) | ℱ k] =ᵐ[μ] (fun _ => 0)

/-- Conditional Hoeffding estimate, including integrability, every real exponential
parameter, and all finite deterministic interval bounds (including degeneracy). -/
def conditional_hoeffding : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ),
    P207.IsMartingale M ℱ μ → ∀ (k : ℕ) (a b : ℝ),
    (∀ᵐ ω ∂μ, a ≤ M (k + 1) ω - M k ω ∧ M (k + 1) ω - M k ω ≤ b) →
    ∀ s : ℝ,
      Integrable (fun ω => Real.exp (s * (M (k + 1) ω - M k ω))) μ ∧
      μ[(fun ω => Real.exp (s * (M (k + 1) ω - M k ω))) | ℱ k] ≤ᵐ[μ]
        (fun _ => Real.exp (s ^ 2 * (b - a) ^ 2 / 8))

end P207.ConditionalHoeffdingSpec
