import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.ControlledIncrementSampling
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.ConditionalExpectation

open MeasureTheory
open scoped MeasureTheory

universe u
namespace P207

/-- The common mean of the increments; index zero is unused. -/
noncomputable def waldMean {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℕ → Ω → ℝ) : ℝ := ∫ ω, Y 1 ω ∂P

/-- `Sₙ = Y₁ + ⋯ + Yₙ`, including the empty sum at time zero. -/
def waldSum {Ω : Type u} (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, Y (k + 1) ω

/-- The centered partial-sum process `Sₙ - μ n`. -/
noncomputable def waldCenteredSum {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  waldSum Y n ω - waldMean P Y * (n : ℝ)

/-- The real stopping time, with zero assigned on the infinite layer.
Its integral agrees with the finite extended expectation under the mean hypothesis. -/
noncomputable def waldTimeReal {Ω : Type u} (τ : Ω → WithTop ℕ) (ω : Ω) : ℝ :=
  (ENat.toENNReal (τ ω)).toReal

namespace WaldFirstSpec

/-- Independence is relative to the given filtration, not just the natural one. -/
def centered_sum_martingale : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m) (Y : ℕ → Ω → ℝ),
    (∀ k, 1 ≤ k → Integrable (Y k) P) →
    (∀ k, 1 ≤ k → Measurable[ℱ k] (Y k)) →
    (∀ k, 1 ≤ k → ProbabilityTheory.IdentDistrib (Y k) (Y 1) P P) →
    (∀ k, 1 ≤ k → ProbabilityTheory.Indep
      (MeasurableSpace.comap (Y k) inferInstance) (ℱ (k - 1)) P) →
    IsMartingale (waldCenteredSum P Y) ℱ P

/-- The source's uniform conditional absolute-increment bound, with its actual constant. -/
def centered_increment_condExp : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m) (Y : ℕ → Ω → ℝ),
    (∀ k, 1 ≤ k → Integrable (Y k) P) →
    (∀ k, 1 ≤ k → Measurable[ℱ k] (Y k)) →
    (∀ k, 1 ≤ k → ProbabilityTheory.IdentDistrib (Y k) (Y 1) P P) →
    (∀ k, 1 ≤ k → ProbabilityTheory.Indep
      (MeasurableSpace.comap (Y k) inferInstance) (ℱ (k - 1)) P) →
    ∀ k, P[(fun ω => |waldCenteredSum P Y (k + 1) ω -
      waldCenteredSum P Y k ω|) | ℱ k] =ᵐ[P]
      fun _ => ∫ ω, |Y 1 ω - waldMean P Y| ∂P

/-- Wald's first identity. The stopped sum equals `Sₙ` on `τ = n` and zero
on `τ = ∞`, which the finite extended mean forces to be null. -/
def wald_first : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m) (Y : ℕ → Ω → ℝ),
    (∀ k, 1 ≤ k → Integrable (Y k) P) →
    (∀ k, 1 ≤ k → Measurable[ℱ k] (Y k)) →
    (∀ k, 1 ≤ k → ProbabilityTheory.IdentDistrib (Y k) (Y 1) P P) →
    (∀ k, 1 ≤ k → ProbabilityTheory.Indep
      (MeasurableSpace.comap (Y k) inferInstance) (ℱ (k - 1)) P) →
    ∀ τ : Ω → WithTop ℕ, IsDiscreteStoppingTime ℱ τ →
    (∫⁻ ω, ENat.toENNReal (τ ω) ∂P) < ⊤ →
    (∀ᵐ ω ∂P, τ ω < ⊤) ∧
    Integrable (waldTimeReal τ) P ∧
    (∫ ω, waldTimeReal τ ω ∂P) = (∫⁻ ω, ENat.toENNReal (τ ω) ∂P).toReal ∧
    Integrable (fullStoppedValue (waldSum Y) τ (fun _ => 0)) P ∧
    (∫ ω, fullStoppedValue (waldSum Y) τ (fun _ => 0) ω ∂P) =
      waldMean P Y * (∫⁻ ω, ENat.toENNReal (τ ω) ∂P).toReal

end WaldFirstSpec
end P207
