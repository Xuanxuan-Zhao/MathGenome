import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Set MeasureTheory
open scoped Interval

namespace Specs.D13Unified.Ch05.Gronwall

/-- The continuous extension at L = 0 of (exp (L v) - 1) / L. -/
noncomputable def EValue (L v : ℝ) : ℝ :=
  if L = 0 then v else (Real.exp (L * v) - 1) / L

def EType := ℝ → ℝ → ℝ

def EFormula : Prop :=
  (∀ v, EValue 0 v = v) ∧
  (∀ L v, 0 < L → EValue L v = (Real.exp (L * v) - 1) / L)

/-- Real-valued representatives are required to be nonnegative only on the stated interval. -/
def Forward : Prop :=
  ∀ (s T A : ℝ) (u b c : ℝ → ℝ), s ≤ T → 0 ≤ A →
    ContinuousOn u (Icc s T) → ContinuousOn b (Icc s T) →
    ContinuousOn c (Icc s T) →
    (∀ r ∈ Icc s T, 0 ≤ u r ∧ 0 ≤ b r ∧ 0 ≤ c r) →
    (∀ t ∈ Icc s T, u t ≤ A + ∫ r in s..t, (b r * u r + c r)) →
    ∀ t ∈ Icc s T,
      u t ≤ A * Real.exp (∫ r in s..t, b r) +
        ∫ r in s..t, c r * Real.exp (∫ q in r..t, b q)

/-- All integrals on the left side of the base time are nonnegatively oriented:
    the hypothesis integrates from t to s, and the kernel from t to r. -/
def Backward : Prop :=
  ∀ (T s A : ℝ) (u b c : ℝ → ℝ), T ≤ s → 0 ≤ A →
    ContinuousOn u (Icc T s) → ContinuousOn b (Icc T s) →
    ContinuousOn c (Icc T s) →
    (∀ r ∈ Icc T s, 0 ≤ u r ∧ 0 ≤ b r ∧ 0 ≤ c r) →
    (∀ t ∈ Icc T s, u t ≤ A + ∫ r in t..s, (b r * u r + c r)) →
    ∀ t ∈ Icc T s,
      u t ≤ A * Real.exp (∫ r in t..s, b r) +
        ∫ r in t..s, c r * Real.exp (∫ q in t..r, b q)

def ConstantForward : Prop :=
  ∀ (s T A L δ : ℝ) (u : ℝ → ℝ), s ≤ T → 0 ≤ A → 0 ≤ L → 0 ≤ δ →
    ContinuousOn u (Icc s T) → (∀ r ∈ Icc s T, 0 ≤ u r) →
    (∀ t ∈ Icc s T, u t ≤ A + ∫ r in s..t, (L * u r + δ)) →
    ∀ t ∈ Icc s T, u t ≤ A * Real.exp (L * (t - s)) + δ * EValue L (t - s)

def ConstantBackward : Prop :=
  ∀ (T s A L δ : ℝ) (u : ℝ → ℝ), T ≤ s → 0 ≤ A → 0 ≤ L → 0 ≤ δ →
    ContinuousOn u (Icc T s) → (∀ r ∈ Icc T s, 0 ≤ u r) →
    (∀ t ∈ Icc T s, u t ≤ A + ∫ r in t..s, (L * u r + δ)) →
    ∀ t ∈ Icc T s, u t ≤ A * Real.exp (L * |t - s|) + δ * EValue L |t - s|

end Specs.D13Unified.Ch05.Gronwall
