import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.SecondMoment
import MathGenome.Internal.ExtremalOptimization.P205.Probability.MomentIdentities
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Second-moment existence bound

For each event B, integrate (X-c)² over B for every real c. The resulting
quadratic in c is nonnegative, so its discriminant is nonpositive. This proves
Cauchy–Schwarz even when B has measure zero. For B = {X > 0}, almost sure
nonnegativity identifies the restricted mean with the full mean. Its positivity
forces a positive second moment, after which division gives the bound.
-/

open MeasureTheory

namespace P205.Probability.SecondMoment

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ}

/-- Restricted Cauchy–Schwarz and comparison with the full second moment. -/
theorem event_cauchy_schwarz (hX : MemLp X 2 μ) {B : Set Ω} (_hB : MeasurableSet B) :
    (∫ ω in B, X ω ∂μ) ^ 2 ≤ μ.real B * (∫ ω in B, X ω ^ 2 ∂μ) ∧
    μ.real B * (∫ ω in B, X ω ^ 2 ∂μ) ≤ μ.real B * (∫ ω, X ω ^ 2 ∂μ) := by
  have h1 := MomentIdentities.first_moment_integrable hX
  have h2 := MomentIdentities.square_integrable hX
  have hquad : ∀ c : ℝ, 0 ≤ μ.real B * (c * c) +
      (-2 * ∫ ω in B, X ω ∂μ) * c + (∫ ω in B, X ω ^ 2 ∂μ) := by
    intro c
    have hpos : 0 ≤ ∫ ω in B, (X ω - c) ^ 2 ∂μ :=
      integral_nonneg (fun _ ↦ sq_nonneg _)
    have hexpand : (fun ω ↦ (X ω - c) ^ 2) =
        (fun ω ↦ X ω ^ 2 - (2 * c) * X ω + c ^ 2) := by
      funext ω
      ring
    rw [hexpand, integral_add (f := fun ω ↦ X ω ^ 2 - (2 * c) * X ω)
      (g := fun _ : Ω ↦ c ^ 2) (h2.restrict.sub (h1.restrict.const_mul _))
      (integrable_const _), integral_sub (f := fun ω ↦ X ω ^ 2)
      (g := fun ω ↦ (2 * c) * X ω) h2.restrict (h1.restrict.const_mul _),
      integral_const_mul, integral_const] at hpos
    simp only [smul_eq_mul, Measure.real, Measure.restrict_apply_univ] at hpos ⊢
    nlinarith only [hpos]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  constructor
  · nlinarith
  · exact mul_le_mul_of_nonneg_left
      (setIntegral_le_integral h2 (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _))
      (measureReal_nonneg)

/-- The second moment is positive and controls the probability of a positive value. -/
theorem second_moment_bound (hXm : Measurable X) (hX : MemLp X 2 μ)
    (hXnonneg : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hmean : 0 < ∫ ω, X ω ∂μ) :
    0 < (∫ ω, X ω ^ 2 ∂μ) ∧
    (∫ ω, X ω ∂μ) ^ 2 / (∫ ω, X ω ^ 2 ∂μ) ≤ μ.real {ω | 0 < X ω} := by
  have hB : MeasurableSet {ω | 0 < X ω} := measurableSet_lt measurable_const hXm
  have hmeanB : (∫ ω in {ω | 0 < X ω}, X ω ∂μ) = ∫ ω, X ω ∂μ := by
    rw [← integral_indicator hB]
    apply integral_congr_ae
    filter_upwards [hXnonneg] with ω hω
    by_cases hpos : 0 < X ω
    · simp [hpos]
    · have hz : X ω = 0 := le_antisymm (le_of_not_gt hpos) hω
      simp [hz]
  have hcs := event_cauchy_schwarz hX hB
  rw [hmeanB] at hcs
  have hle := hcs.1.trans hcs.2
  have hsecond : 0 < ∫ ω, X ω ^ 2 ∂μ := by
    by_contra h
    have hn : μ.real {ω | 0 < X ω} * (∫ ω, X ω ^ 2 ∂μ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos measureReal_nonneg (le_of_not_gt h)
    nlinarith [sq_pos_of_pos hmean]
  exact ⟨hsecond, (div_le_iff₀ hsecond).2 (by nlinarith [hle])⟩

end P205.Probability.SecondMoment
