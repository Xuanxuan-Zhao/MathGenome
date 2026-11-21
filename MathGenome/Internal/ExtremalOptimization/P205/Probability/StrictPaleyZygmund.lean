import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.StrictPaleyZygmund
import MathGenome.Internal.ExtremalOptimization.P205.Probability.SecondMoment

/-!
# Strict Paley–Zygmund inequality

The integral on the complement of the strict upper event is at most θ EX.
The remaining integral is therefore at least (1-θ) EX. Event-restricted
Cauchy–Schwarz and positivity of the second moment give the stated bound.
-/

open MeasureTheory

namespace P205.Probability.StrictPaleyZygmund

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ}

/-- Paley–Zygmund for a strict threshold, including θ = 0. -/
theorem strict_paley_zygmund_bound (hXm : Measurable X) (hX : MemLp X 2 μ)
    (hXnonneg : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hmean : 0 < ∫ ω, X ω ∂μ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    (1 - θ) ^ 2 * (∫ ω, X ω ∂μ) ^ 2 / (∫ ω, X ω ^ 2 ∂μ) ≤
      μ.real {ω | θ * (∫ x, X x ∂μ) < X ω} := by
  let B : Set Ω := {ω | θ * (∫ x, X x ∂μ) < X ω}
  have hB : MeasurableSet B := measurableSet_lt measurable_const hXm
  have h1 := MomentIdentities.first_moment_integrable hX
  have hsmall : (∫ ω in Bᶜ, X ω ∂μ) ≤ θ * (∫ ω, X ω ∂μ) := by
    calc
      (∫ ω in Bᶜ, X ω ∂μ) ≤ ∫ _ in Bᶜ, θ * (∫ ω, X ω ∂μ) ∂μ := by
        apply setIntegral_mono_on h1.integrableOn (integrable_const _) hB.compl
        intro ω hω
        exact le_of_not_gt hω
      _ = μ.real Bᶜ * (θ * (∫ ω, X ω ∂μ)) := by
        rw [setIntegral_const, smul_eq_mul]
      _ ≤ θ * (∫ ω, X ω ∂μ) :=
        mul_le_of_le_one_left (mul_nonneg hθ0 hmean.le) measureReal_le_one
  have hsplit := integral_add_compl hB h1
  have hlower : (1 - θ) * (∫ ω, X ω ∂μ) ≤ ∫ ω in B, X ω ∂μ := by
    linarith
  have hnonneg : 0 ≤ (1 - θ) * (∫ ω, X ω ∂μ) :=
    mul_nonneg (sub_nonneg.mpr hθ1.le) hmean.le
  have hsq : ((1 - θ) * (∫ ω, X ω ∂μ)) ^ 2 ≤ (∫ ω in B, X ω ∂μ) ^ 2 :=
    pow_le_pow_left₀ hnonneg hlower 2
  have hcs := SecondMoment.event_cauchy_schwarz hX hB
  have hsecond := (SecondMoment.second_moment_bound hXm hX hXnonneg hmean).1
  apply (div_le_iff₀ hsecond).2
  have hbound := hsq.trans (hcs.1.trans hcs.2)
  dsimp only [B] at hbound
  nlinarith only [hbound]

end P205.Probability.StrictPaleyZygmund
