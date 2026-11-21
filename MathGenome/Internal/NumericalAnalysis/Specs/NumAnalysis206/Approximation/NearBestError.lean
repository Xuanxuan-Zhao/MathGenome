import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.InterpolationNorm

/-! Independent specifications for the near-best inequality in paper.tex, W52.
The infimum ranges over all real polynomials of degree at most `n`, including
zero, evaluated on the same interval and with the same uniform norm as the
interpolation operator. No minimizing polynomial is assumed to exist. -/

noncomputable section
open Polynomial

namespace Specs.NumAnalysis206.Approximation
open _root_.NumAnalysis206.Approximation

def bestApproximationErrorValue {a b : ℝ} (n : ℕ) (f : IntervalContinuous a b) : ℝ :=
  sInf {r : ℝ | ∃ p : ℝ[X], p.degree ≤ (n : WithBot ℕ) ∧
    ‖f - p.toContinuousMapOn (Set.Icc a b)‖ = r}

def bestApproximationErrorType :=
  ∀ {a b : ℝ}, ℕ → IntervalContinuous a b → ℝ

def nearBestError : Prop :=
  ∀ {a b : ℝ} {n : ℕ} (x : Fin (n + 1) → Set.Icc a b), a < b →
    Function.Injective x → ∀ f : IntervalContinuous a b,
      ‖f - interpolationOperatorValue x f‖ ≤
        (1 + lebesgueConstantValue x) * bestApproximationErrorValue n f

end Specs.NumAnalysis206.Approximation
