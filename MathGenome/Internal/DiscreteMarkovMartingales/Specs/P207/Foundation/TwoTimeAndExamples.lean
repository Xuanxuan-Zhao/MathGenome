import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.ProcessInterfaces
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.ConditionalExpectation

open MeasureTheory
open scoped MeasureTheory

universe u
namespace P207.TwoTimeAndExamplesSpec

/-- The source's one-step definition agrees with the library all-pairs definition. -/
def martingale_iff_library : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ),
    P207.IsMartingale X ℱ μ ↔ Martingale X ℱ μ

def submartingale_iff_library : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ),
    P207.IsSubmartingale X ℱ μ ↔ Submartingale X ℱ μ

/-- Includes the diagonal i = j. Adaptation and integrability are the source's standing hypotheses. -/
def martingale_two_time : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ),
    Adapted ℱ X → (∀ n, Integrable (X n) μ) →
    ((∀ n, μ[X (n + 1) | ℱ n] =ᵐ[μ] X n) ↔
      ∀ i j, i ≤ j → μ[X j | ℱ i] =ᵐ[μ] X i)

def submartingale_two_time : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ),
    Adapted ℱ X → (∀ n, Integrable (X n) μ) →
    ((∀ n, X n ≤ᵐ[μ] μ[X (n + 1) | ℱ n]) ↔
      ∀ i j, i ≤ j → X i ≤ᵐ[μ] μ[X j | ℱ i])

/-- All countably many two-time relations hold outside one null set. -/
def martingale_simultaneous : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ),
    P207.IsMartingale X ℱ μ →
      ∀ᵐ ω ∂μ, ∀ i j, i ≤ j → μ[X j | ℱ i] ω = X i ω

def submartingale_simultaneous : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ),
    P207.IsSubmartingale X ℱ μ →
      ∀ᵐ ω ∂μ, ∀ i j, i ≤ j → X i ω ≤ μ[X j | ℱ i] ω

/-- Sum over k = 1,...,n, written with k+1 over range n; in particular M₀ = 0.
Independence is between σ(ξₖ) and the preceding sigma-algebra. No condition is imposed on ξ₀. -/
def centered_independent_sum : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (ξ : ℕ → Ω → ℝ),
    (∀ k, 1 ≤ k → Integrable (ξ k) μ) →
    (∀ k, 1 ≤ k → Measurable[ℱ k] (ξ k)) →
    (∀ k, 1 ≤ k → (∫ ω, ξ k ω ∂μ) = 0) →
    (∀ k, 1 ≤ k → ProbabilityTheory.Indep
      (MeasurableSpace.comap (ξ k) inferInstance) (ℱ (k - 1)) μ) →
    P207.IsMartingale (fun n ω => ∑ k ∈ Finset.range n, ξ (k + 1) ω) ℱ μ

def conditional_expectation_process : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (Y : Ω → ℝ), Integrable Y μ →
    P207.IsMartingale (fun n => μ[Y | ℱ n]) ℱ μ

end P207.TwoTimeAndExamplesSpec
