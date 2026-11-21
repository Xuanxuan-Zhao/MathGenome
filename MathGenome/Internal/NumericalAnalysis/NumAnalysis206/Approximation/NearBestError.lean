import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.NearBestError
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.InterpolationNorm
import Mathlib.Tactic.Abel

/-! The near-best conclusion of W52, using the interpolation norm equality
and polynomial reproduction from `InterpolationNorm`. -/

noncomputable section
open Polynomial

namespace NumAnalysis206.Approximation

/-- The infimum of uniform errors over every polynomial of degree at most `n`. -/
def bestApproximationError {a b : ℝ} (n : ℕ) (f : IntervalContinuous a b) : ℝ :=
  Specs.NumAnalysis206.Approximation.bestApproximationErrorValue n f

variable {a b : ℝ} {n : ℕ} (x : Fin (n + 1) → Set.Icc a b)

/-- Polynomial reproduction gives the error estimate for each approximant. -/
theorem interpolation_error_le (hab : a < b) (hx : Function.Injective x)
    (f : IntervalContinuous a b) (p : ℝ[X]) (hp : p.degree ≤ (n : WithBot ℕ)) :
    ‖f - interpolationOperator x f‖ ≤
      (1 + lebesgueConstant x) * ‖f - p.toContinuousMapOn (Set.Icc a b)‖ := by
  have herr : f - interpolationOperator x f =
      (f - p.toContinuousMapOn (Set.Icc a b)) -
        interpolationOperator x (f - p.toContinuousMapOn (Set.Icc a b)) := by
    rw [map_sub, interpolation_reproduces x hx p hp]
    abel
  rw [herr]
  calc
    _ ≤ ‖f - p.toContinuousMapOn (Set.Icc a b)‖ +
        ‖interpolationOperator x (f - p.toContinuousMapOn (Set.Icc a b))‖ :=
      norm_sub_le _ _
    _ ≤ ‖f - p.toContinuousMapOn (Set.Icc a b)‖ +
        ‖interpolationOperator x‖ * ‖f - p.toContinuousMapOn (Set.Icc a b)‖ :=
      add_le_add le_rfl ((interpolationOperator x).le_opNorm
        (f - p.toContinuousMapOn (Set.Icc a b)))
    _ = _ := by rw [interpolation_norm x hab hx, add_mul, one_mul]

/-- W52: take the infimum over all degree-at-most-`n` polynomials, without
requiring that any polynomial attains the infimum. -/
theorem near_best_error (hab : a < b) (hx : Function.Injective x)
    (f : IntervalContinuous a b) :
    ‖f - interpolationOperator x f‖ ≤
      (1 + lebesgueConstant x) * bestApproximationError n f := by
  have hc : 0 < 1 + lebesgueConstant x :=
    add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg (lebesgueFunction x))
  rw [mul_comm]
  apply (div_le_iff₀ hc).mp
  change ‖f - interpolationOperator x f‖ / (1 + lebesgueConstant x) ≤
    sInf {r : ℝ | ∃ p : ℝ[X], p.degree ≤ (n : WithBot ℕ) ∧
      ‖f - p.toContinuousMapOn (Set.Icc a b)‖ = r}
  apply le_csInf
  · exact ⟨‖f - (0 : ℝ[X]).toContinuousMapOn (Set.Icc a b)‖, 0, by simp⟩
  · rintro r ⟨p, hp, rfl⟩
    apply (div_le_iff₀ hc).mpr
    rw [mul_comm]
    exact interpolation_error_le x hab hx f p hp

end NumAnalysis206.Approximation
