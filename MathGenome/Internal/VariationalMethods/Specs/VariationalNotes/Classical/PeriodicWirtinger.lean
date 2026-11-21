import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
open MeasureTheory

namespace Specs.VariationalNotes.Classical.PeriodicWirtinger

/-- The scalar C¹, periodic, mean-zero class from Lemma v07-08-01. -/
def Admissible (T : ℝ) (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 f ∧ Function.Periodic f T ∧ (∫ t in (0 : ℝ)..T, f t) = 0

/-- The sharp inequality and its complete equality classification. -/
def Statement : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ (f : ℝ → ℝ), Admissible T f →
    (∫ t in (0 : ℝ)..T, |f t| ^ 2) ≤
        (T / (2 * Real.pi)) ^ 2 * (∫ t in (0 : ℝ)..T, |deriv f t| ^ 2) ∧
    ((∫ t in (0 : ℝ)..T, |f t| ^ 2) =
        (T / (2 * Real.pi)) ^ 2 * (∫ t in (0 : ℝ)..T, |deriv f t| ^ 2) ↔
      ∃ A B : ℝ, ∀ t : ℝ,
        f t = A * Real.cos (2 * Real.pi * t / T) +
          B * Real.sin (2 * Real.pi * t / T))

end Specs.VariationalNotes.Classical.PeriodicWirtinger
