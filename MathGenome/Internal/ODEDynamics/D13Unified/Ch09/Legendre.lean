import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch09.Legendre
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace D13Unified.Ch09.Legendre
open Polynomial

lemma solution_iff (m : ℕ) (p : ℝ[X]) :
    IsLegendreSolution m p ↔
      (X ^ 2 - 1) * p.derivative.derivative + 2 * X * p.derivative =
        C (eigenvalue m) * p := by
  unfold IsLegendreSolution
  simp only [derivative_mul, derivative_sub, derivative_one, derivative_pow,
    derivative_X, mul_one, zero_sub]
  norm_num
  simp only [C_ofNat]
  constructor <;> intro h <;> linear_combination -h

lemma coeff_euler (p : ℝ[X]) (n : ℕ) :
    (X * p.derivative).coeff n = (n : ℝ) * p.coeff n := by
  cases n with
  | zero => simp
  | succ n => simp [coeff_derivative, mul_comm]

lemma eigenvalue_injective : Function.Injective eigenvalue := by
  intro m n h
  unfold eigenvalue at h
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have he : (m : ℝ) = n := by nlinarith
  exact_mod_cast he

lemma raising_solution (m : ℕ) (p : ℝ[X]) (h : IsLegendreSolution m p) :
    IsLegendreSolution (m+1)
      ((X ^ 2 - 1) * p.derivative + C ((m : ℝ) + 1) * X * p) := by
  have hp := (solution_iff m p).mp h
  have hd := congrArg derivative hp
  rw [solution_iff]
  simp only [derivative_sub, derivative_mul, derivative_pow,
    derivative_X, derivative_one, derivative_ofNat,
    zero_mul, mul_one, add_zero, zero_add, sub_zero,
    eigenvalue, map_add, map_mul, map_natCast, map_one, Nat.cast_add,
    Nat.cast_one] at hp hd ⊢
  norm_num at hd ⊢
  linear_combination (X ^ 2 - 1) * hd + ((m : ℝ[X]) + 3) * X * hp

/-- Coefficients of the raising construction, written with an Euler operator. -/
lemma raising_eq (m : ℕ) (p : ℝ[X]) :
    (X ^ 2 - 1) * p.derivative + C ((m : ℝ) + 1) * X * p =
      X * (X * p.derivative + C ((m : ℝ) + 1) * p) - p.derivative := by
  ring

lemma raising_coeff (m : ℕ) (p : ℝ[X]) (n : ℕ) :
    (((X ^ 2 - 1) * p.derivative + C ((m : ℝ) + 1) * X * p).coeff (n+1)) =
      ((n : ℝ) + (m : ℝ) + 1) * p.coeff n -
        p.coeff (n+2) * ((n : ℝ) + 2) := by
  rw [raising_eq, coeff_sub, coeff_X_mul, coeff_add, coeff_euler, coeff_C_mul,
    coeff_derivative]
  push_cast
  ring

lemma raising_degree (m : ℕ) (p : ℝ[X]) (hp : p.natDegree = m) (hne : p ≠ 0) :
    let q := (X ^ 2 - 1) * p.derivative + C ((m : ℝ) + 1) * X * p
    q ≠ 0 ∧ q.natDegree = m+1 := by
  dsimp only
  have hz : ∀ k, m < k → p.coeff k = 0 := fun k hk =>
    coeff_eq_zero_of_natDegree_lt (hp ▸ hk)
  have hc : p.coeff m ≠ 0 := by
    rw [← hp, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hne
  have htop :
      (((X ^ 2 - 1) * p.derivative + C ((m : ℝ) + 1) * X * p).coeff (m+1)) ≠ 0 := by
    rw [raising_coeff, hz (m+2) (by omega), zero_mul, sub_zero]
    exact mul_ne_zero (by positivity) hc
  have hle :
      ((X ^ 2 - 1) * p.derivative + C ((m : ℝ) + 1) * X * p).natDegree ≤ m+1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    obtain ⟨n, rfl⟩ : ∃ n, k = n+1 := ⟨k-1, by omega⟩
    rw [raising_coeff, hz n (by omega), hz (n+2) (by omega)]
    ring
  exact ⟨fun hq => htop (by rw [hq, coeff_zero]),
    natDegree_eq_of_le_of_coeff_ne_zero hle htop⟩

theorem legendre_polynomial :
    Specs.D13Unified.Ch09.Legendre.legendre_polynomial_type := by
  intro m
  induction m with
  | zero => simp [legendre, IsLegendreSolution, eigenvalue]
  | succ m ih =>
    obtain ⟨hne, hdeg⟩ := raising_degree m (legendre m) ih.2.1 ih.1
    exact ⟨hne, hdeg, raising_solution m (legendre m) ih.2.2⟩

/-- The original differential equation forces its coefficient recurrence. -/
lemma solution_coefficients (m : ℕ) (p : ℝ[X]) (h : IsLegendreSolution m p) (n : ℕ) :
    ((n : ℝ) + 2) * ((n : ℝ) + 1) * p.coeff (n+2) =
      ((n : ℝ) * ((n : ℝ) + 1) - eigenvalue m) * p.coeff n := by
  have hp := (solution_iff m p).mp h
  have he : X * (X * p.derivative).derivative + X * p.derivative -
      p.derivative.derivative = C (eigenvalue m) * p := by
    simp only [derivative_mul, derivative_X, one_mul]
    linear_combination hp
  have hc := congrArg (fun q : ℝ[X] => q.coeff n) he
  simp only [coeff_add, coeff_sub, coeff_euler, coeff_derivative, coeff_C_mul] at hc
  push_cast at hc
  linear_combination -hc

lemma degree_of_solution (m : ℕ) (p : ℝ[X]) (h : IsLegendreSolution m p)
    (hp : p ≠ 0) : p.natDegree = m := by
  have hc : p.coeff p.natDegree ≠ 0 := by
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hp
  have he := solution_coefficients m p h p.natDegree
  rw [coeff_eq_zero_of_natDegree_lt (by omega), mul_zero] at he
  have he' : (p.natDegree : ℝ) * ((p.natDegree : ℝ) + 1) - eigenvalue m = 0 :=
    (mul_eq_zero.mp he.symm).resolve_right hc
  exact eigenvalue_injective (sub_eq_zero.mp he')

lemma solution_sub_const_mul (m : ℕ) (p q : ℝ[X]) (c : ℝ)
    (hp : IsLegendreSolution m p) (hq : IsLegendreSolution m q) :
    IsLegendreSolution m (p - C c * q) := by
  rw [solution_iff] at hp hq ⊢
  simp only [derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add]
  linear_combination hp - C c * hq

theorem polynomial_solution_unique :
    Specs.D13Unified.Ch09.Legendre.polynomial_solution_unique_type := by
  intro m p hp
  have hl := legendre_polynomial m
  have hc : (legendre m).coeff m ≠ 0 := by
    have ht := leadingCoeff_ne_zero.mpr hl.1
    rwa [← coeff_natDegree, hl.2.1] at ht
  let c := p.coeff m / (legendre m).coeff m
  have hr := solution_sub_const_mul m p (legendre m) c hp hl.2.2
  have hz : (p - C c * legendre m).coeff m = 0 := by
    simp only [coeff_sub, coeff_C_mul, c]
    field_simp
    ring
  have heq : p - C c * legendre m = 0 := by
    by_contra hne
    have hd := degree_of_solution m _ hr hne
    have htop := leadingCoeff_ne_zero.mpr hne
    rw [← coeff_natDegree, hd, hz] at htop
    exact htop rfl
  exact ⟨c, sub_eq_zero.mp heq⟩

theorem nonzero_solutions_proportional :
    Specs.D13Unified.Ch09.Legendre.nonzero_solutions_proportional_type := by
  intro m p q hp hq hps hqs
  obtain ⟨a, ha⟩ := polynomial_solution_unique m p hps
  obtain ⟨b, hb⟩ := polynomial_solution_unique m q hqs
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hp
    simp [ha, ha0]
  have hb0 : b ≠ 0 := by
    intro hb0
    apply hq
    simp [hb, hb0]
  refine ⟨a / b, div_ne_zero ha0 hb0, ?_⟩
  rw [ha, hb, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ hb0]

/-- The polynomial Wronskian identity needs no nondegeneracy at ±1. -/
lemma wronskian_identity (m l : ℕ) (p q : ℝ[X])
    (hp : IsLegendreSolution m p) (hq : IsLegendreSolution l q) :
    derivative ((1 - X ^ 2) * (p.derivative * q - p * q.derivative)) =
      C (eigenvalue l - eigenvalue m) * (p * q) := by
  rw [solution_iff] at hp hq
  simp only [derivative_mul, derivative_one, derivative_pow,
    derivative_X, mul_one, zero_sub, map_sub]
  norm_num
  simp only [C_ofNat]
  linear_combination -q * hp + p * hq

theorem polynomial_solutions_orthogonal :
    Specs.D13Unified.Ch09.Legendre.polynomial_solutions_orthogonal_type := by
  intro m l p q hml hp hq
  let W : ℝ[X] := (1 - X ^ 2) * (p.derivative * q - p * q.derivative)
  have hd : W.derivative = C (eigenvalue l - eigenvalue m) * (p * q) :=
    wronskian_identity m l p q hp hq
  have hi : (∫ x : ℝ in (-1)..1, W.derivative.eval x) = W.eval 1 - W.eval (-1) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => W.hasDerivAt x) (W.derivative.differentiable.continuous.intervalIntegrable _ _)
  have hright : W.eval 1 = 0 := by simp [W]
  have hleft : W.eval (-1) = 0 := by simp [W]
  rw [hd, hright, hleft] at hi
  simp only [eval_mul, eval_C, sub_self, intervalIntegral.integral_const_mul] at hi
  exact (mul_eq_zero.mp hi).resolve_left
    (sub_ne_zero.mpr (fun he => hml (eigenvalue_injective he).symm))

theorem legendre_orthogonal : Specs.D13Unified.Ch09.Legendre.legendre_orthogonal_type := by
  intro m l hml
  exact polynomial_solutions_orthogonal m l (legendre m) (legendre l) hml
    (legendre_polynomial m).2.2 (legendre_polynomial l).2.2

end D13Unified.Ch09.Legendre
