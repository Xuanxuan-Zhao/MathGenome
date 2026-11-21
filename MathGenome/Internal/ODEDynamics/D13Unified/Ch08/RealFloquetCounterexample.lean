import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch08.RealFloquetCounterexample
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open scoped Matrix Matrix.Norms.Operator
open Specs.D13Unified.Ch07.MatrixExponential (exponentialValue)

namespace D13Unified.Ch08.RealFloquetCounterexample

set_option maxRecDepth 2000

lemma rotation_mul_reverse (t : ℝ) : R t * R (-t) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [R, Matrix.mul_apply, Fin.sum_univ_two, mul_neg] <;> nlinarith [Real.sin_sq_add_cos_sq (Real.pi * t)]

lemma rotation_inv (t : ℝ) : (R t)⁻¹ = R (-t) :=
  Matrix.inv_eq_right_inv (rotation_mul_reverse t)

lemma rotation_shift (t : ℝ) : R (t + 1) = -R t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [R, mul_add, Real.sin_add_pi, Real.cos_add_pi]

lemma continuous_rotation : Continuous R := by
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  fin_cases i <;> fin_cases j <;>
    simp [R] <;> fun_prop

lemma continuous_coefficient : Continuous A := by
  unfold A
  simp_rw [rotation_inv]
  exact continuous_const.add ((continuous_rotation.mul continuous_const).mul
    (continuous_rotation.comp continuous_neg))

lemma coefficient_periodic : Function.Periodic A 1 := by
  intro t
  have hr : R (-(t + 1)) = -R (-t) := by
    have hh := rotation_shift (-(t + 1))
    have ht : -(t + 1) + 1 = -t := by ring
    rw [ht] at hh
    exact neg_eq_iff_eq_neg.mp hh.symm
  unfold A
  rw [rotation_inv (t + 1), rotation_inv t, rotation_shift, hr]
  simp

lemma initial_value : X 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [X, R, Matrix.mul_apply, Fin.sum_univ_two]

lemma monodromy : X 1 = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [X, R, M, Matrix.mul_apply, Fin.sum_univ_two]

lemma solution_derivative (t : ℝ) : HasDerivAt X (A t * X t) t := by
  have hs : HasDerivAt (fun r : ℝ => Real.sin (Real.pi * r))
      (Real.cos (Real.pi * t) * Real.pi) t := by
    simpa using ((hasDerivAt_id t).const_mul Real.pi).sin
  have hc : HasDerivAt (fun r : ℝ => Real.cos (Real.pi * r))
      (-Real.sin (Real.pi * t) * Real.pi) t := by
    simpa using ((hasDerivAt_id t).const_mul Real.pi).cos
  have hq : HasDerivAt (fun r : ℝ => (2 : ℝ) ^ r)
      ((2 : ℝ) ^ t * Real.log 2) t :=
    (Real.hasStrictDerivAt_const_rpow (by norm_num : (0 : ℝ) < 2) t).hasDerivAt
  have hr : (R t)⁻¹ * R t = 1 := by
    rw [rotation_inv]
    simpa using rotation_mul_reverse (-t)
  have hAX : A t * X t =
      Real.pi • (!![0, -1; 1, 0] * (R t * !![1, 0; 0, (2 : ℝ) ^ t])) +
        R t * (!![0, 0; 0, Real.log 2] * !![1, 0; 0, (2 : ℝ) ^ t]) := by
    simp only [A, X, add_mul, smul_mul_assoc, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (R t)⁻¹ (R t), hr, Matrix.one_mul]
  rw [hAX]
  apply hasDerivAt_pi.mpr; intro i
  apply hasDerivAt_pi.mpr; intro j
  fin_cases i <;> fin_cases j
  all_goals simp [X, R, Matrix.mul_apply, Fin.sum_univ_two]
  · convert hc using 1; ring
  · convert hs.neg.mul hq using 1
    · ext r; simp
    · simp; ring
  · convert hs using 1; ring
  · convert hc.mul hq using 1; ring

lemma solution_isUnit (t : ℝ) : IsUnit (X t) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [X, Matrix.det_mul]
  have hr : (R t).det = 1 := by
    simp [R, Matrix.det_fin_two]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * t)]
  rw [hr, one_mul]
  simpa [Matrix.det_fin_two, isUnit_iff_ne_zero] using
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) t).ne'

lemma no_real_logarithm (B : Mat) : exponentialValue B 1 ≠ M := by
  intro h
  have he : NormedSpace.exp B = M := by simpa [exponentialValue] using h
  have hc : B * M = M * B := by
    simpa only [he] using (Commute.refl B).exp_right.eq
  have h01 : B 0 1 = 0 := by
    have hh := congrArg (fun C : Mat => C 0 1) hc
    simp [M, Matrix.mul_apply, Fin.sum_univ_two] at hh
    linarith
  have h10 : B 1 0 = 0 := by
    have hh := congrArg (fun C : Mat => C 1 0) hc
    simp [M, Matrix.mul_apply, Fin.sum_univ_two] at hh
    linarith
  have hb : B = Matrix.diagonal (fun i => B i i) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10]
  rw [hb, Matrix.exp_diagonal] at he
  have hh := congrArg (fun C : Mat => C 0 0) he
  have hp := Real.exp_pos (B 0 0)
  simp [M, ← Real.exp_eq_exp_ℝ] at hh
  linarith

lemma no_real_factorization :
    ¬ ∃ (P : ℝ → Mat) (B : Mat), Function.Periodic P 1 ∧
      (∀ t : ℝ, IsUnit (P t)) ∧ ∀ t : ℝ, X t = P t * exponentialValue B t := by
  rintro ⟨P, B, hP, _hunit, hx⟩
  have h0 : P 0 = 1 := by
    simpa [initial_value, exponentialValue] using (hx 0).symm
  have h1 : P 1 = 1 := by simpa using (hP 0).trans h0
  have hm : exponentialValue B 1 = M := by
    simpa [h1, monodromy] using (hx 1).symm
  exact no_real_logarithm B hm

/-- The explicit real period-one system has no real period-one Floquet factorization. -/
theorem counterexample :
    Specs.D13Unified.Ch08.RealFloquetCounterexample.Counterexample := by
  exact ⟨continuous_coefficient, coefficient_periodic, initial_value, solution_derivative,
    solution_isUnit, monodromy, no_real_logarithm, no_real_factorization⟩

end D13Unified.Ch08.RealFloquetCounterexample
