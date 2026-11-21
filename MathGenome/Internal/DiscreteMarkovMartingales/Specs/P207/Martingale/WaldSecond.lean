import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.WaldFirst
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped MeasureTheory
universe u
namespace P207.WaldSecondSpec

/-- Wald's second identity for the centered stopped process. The terminal
assignment is arbitrary because the finite-mean stopping time is finite a.s. -/
def wald_second_centered : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m) (Y : ℕ → Ω → ℝ),
    (∀ k, 1 ≤ k → Integrable (Y k) P) →
    (∀ k, 1 ≤ k → Measurable[ℱ k] (Y k)) →
    (∀ k, 1 ≤ k → ProbabilityTheory.IdentDistrib (Y k) (Y 1) P P) →
    (∀ k, 1 ≤ k → ProbabilityTheory.Indep
      (MeasurableSpace.comap (Y k) inferInstance) (ℱ (k - 1)) P) →
    Integrable (fun ω => (Y 1 ω - waldMean P Y) ^ 2) P →
    ∀ (τ : Ω → WithTop ℕ), IsDiscreteStoppingTime ℱ τ →
    (∫⁻ ω, ENat.toENNReal (τ ω) ∂P) < ⊤ →
    ∀ (A : Ω → ℝ),
    MemLp (fullStoppedValue (waldCenteredSum P Y) τ A) 2 P ∧
    (∫ ω, fullStoppedValue (waldCenteredSum P Y) τ A ω ^ 2 ∂P) =
      (∫ ω, (Y 1 ω - waldMean P Y) ^ 2 ∂P) *
        (∫⁻ ω, ENat.toENNReal (τ ω) ∂P).toReal

/-- The same identity written literally as `Sτ - μτ`; no L² hypothesis on τ.
The stopped sum can have any assignment on the infinite layer. -/
def wald_second : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m) (Y : ℕ → Ω → ℝ),
    (∀ k, 1 ≤ k → Integrable (Y k) P) →
    (∀ k, 1 ≤ k → Measurable[ℱ k] (Y k)) →
    (∀ k, 1 ≤ k → ProbabilityTheory.IdentDistrib (Y k) (Y 1) P P) →
    (∀ k, 1 ≤ k → ProbabilityTheory.Indep
      (MeasurableSpace.comap (Y k) inferInstance) (ℱ (k - 1)) P) →
    Integrable (fun ω => (Y 1 ω - waldMean P Y) ^ 2) P →
    ∀ (τ : Ω → WithTop ℕ), IsDiscreteStoppingTime ℱ τ →
    (∫⁻ ω, ENat.toENNReal (τ ω) ∂P) < ⊤ →
    ∀ (A : Ω → ℝ),
    MemLp (fun ω => fullStoppedValue (waldSum Y) τ A ω -
      waldMean P Y * waldTimeReal τ ω) 2 P ∧
    (∫ ω, (fullStoppedValue (waldSum Y) τ A ω -
      waldMean P Y * waldTimeReal τ ω) ^ 2 ∂P) =
      (∫ ω, (Y 1 ω - waldMean P Y) ^ 2 ∂P) *
        (∫⁻ ω, ENat.toENNReal (τ ω) ∂P).toReal

end P207.WaldSecondSpec
