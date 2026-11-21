import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Set MeasureTheory
open scoped Interval

namespace Specs.D13Unified.Ch05.VariableGronwall

/-- The variable-bound Gronwall estimate for continuous nonnegative functions.
No differentiability of the initial bound `a` is required. -/
def Forward : Prop :=
  ∀ (s T : ℝ) (u b a : ℝ → ℝ), s ≤ T →
    ContinuousOn u (Icc s T) → ContinuousOn b (Icc s T) →
    ContinuousOn a (Icc s T) →
    (∀ r ∈ Icc s T, 0 ≤ u r ∧ 0 ≤ b r ∧ 0 ≤ a r) →
    (∀ t ∈ Icc s T, u t ≤ a t + ∫ r in s..t, b r * u r) →
    ∀ t ∈ Icc s T,
      u t ≤ a t + ∫ r in s..t, a r * b r * Real.exp (∫ q in r..t, b q)

/-- For a nondecreasing bound, the full envelope in the preceding estimate
is bounded by the usual exponential expression. -/
def MonotoneEnvelope : Prop :=
  ∀ (s T : ℝ) (b a : ℝ → ℝ), s ≤ T →
    ContinuousOn b (Icc s T) → ContinuousOn a (Icc s T) →
    (∀ r ∈ Icc s T, 0 ≤ b r ∧ 0 ≤ a r) →
    MonotoneOn a (Icc s T) →
    ∀ t ∈ Icc s T,
      a t + (∫ r in s..t, a r * b r * Real.exp (∫ q in r..t, b q)) ≤
        a t * Real.exp (∫ r in s..t, b r)

/-- The resulting estimate for `u` when `a` is nondecreasing. -/
def MonotoneBound : Prop :=
  ∀ (s T : ℝ) (u b a : ℝ → ℝ), s ≤ T →
    ContinuousOn u (Icc s T) → ContinuousOn b (Icc s T) →
    ContinuousOn a (Icc s T) →
    (∀ r ∈ Icc s T, 0 ≤ u r ∧ 0 ≤ b r ∧ 0 ≤ a r) →
    (∀ t ∈ Icc s T, u t ≤ a t + ∫ r in s..t, b r * u r) →
    MonotoneOn a (Icc s T) →
    ∀ t ∈ Icc s T, u t ≤ a t * Real.exp (∫ r in s..t, b r)

end Specs.D13Unified.Ch05.VariableGronwall
