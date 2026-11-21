import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Counting.StirlingFirst
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Counting.StirlingFallingExpansion
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace FiniteCombinatorics.StirlingFallingExpansion

open Polynomial
open scoped BigOperators
open StirlingFirst

/-- The signed recurrence, with its top and out-of-range entries included. -/
theorem signed_stirlingFirst_succ (n k : ℕ) :
    (-1 : ℤ) ^ (n + 1 - (k + 1)) * (stirlingFirst (n + 1) (k + 1) : ℤ) =
      (-1 : ℤ) ^ (n - k) * (stirlingFirst n k : ℤ) -
        (-1 : ℤ) ^ (n - (k + 1)) * (stirlingFirst n (k + 1) : ℤ) * n := by
  rw [stirlingFirst_succ_succ, Nat.cast_add, Nat.cast_mul, Nat.add_sub_add_right]
  by_cases hk : k < n
  · have he : n - k = (n - (k + 1)) + 1 := by omega
    rw [he, pow_succ]
    ring
  · have hz : stirlingFirst n (k + 1) = 0 :=
      stirlingFirst_eq_zero_of_lt n (k + 1) (by omega)
    simp [hz]

/-- Each coefficient of the falling factorial, including those above its degree. -/
theorem coeff_fallingFactorial (n k : ℕ) :
    (∏ i ∈ Finset.range n, (X - C (i : ℤ))).coeff k =
      (-1 : ℤ) ^ (n - k) * (stirlingFirst n k : ℤ) := by
  induction n generalizing k with
  | zero =>
    cases k <;> simp [coeff_one]
  | succ n ih =>
    rw [Finset.prod_range_succ, mul_sub, coeff_sub]
    cases k with
    | zero =>
      rw [coeff_mul_X_zero, coeff_mul_C, ih]
      cases n <;> simp
    | succ k =>
      rw [coeff_mul_X, coeff_mul_C, ih, ih]
      exact (signed_stirlingFirst_succ n k).symm

/-- The signed first Stirling expansion of the falling factorial in ℤ[X]. -/
theorem fallingFactorial_eq_sum (n : ℕ) :
    (∏ i ∈ Finset.range n, (X - C (i : ℤ))) =
      ∑ k ∈ Finset.range (n + 1),
        C ((-1 : ℤ) ^ (n - k) * (stirlingFirst n k : ℤ)) * X ^ k := by
  ext k
  rw [coeff_fallingFactorial]
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hk : k < n + 1
  · simp [hk]
  · simp [hk, stirlingFirst_eq_zero_of_lt n k (by omega)]

/-- Change coefficients without changing the signed integer coefficient formula. -/
theorem map_fallingFactorial_eq_sum {R : Type*} [CommRing R]
    (f : ℤ →+* R) (n : ℕ) :
    Polynomial.map f (∏ i ∈ Finset.range n, (X - C (i : ℤ))) =
      ∑ k ∈ Finset.range (n + 1),
        C (f ((-1 : ℤ) ^ (n - k) * (stirlingFirst n k : ℤ))) * X ^ k := by
  rw [fallingFactorial_eq_sum]
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X]

/-- The falling-factorial identity over an arbitrary commutative ring. -/
theorem fallingFactorial_eq_sum_ring {R : Type*} [CommRing R] (n : ℕ) :
    (∏ i ∈ Finset.range n, (X - C (i : R))) =
      ∑ k ∈ Finset.range (n + 1),
        C (((-1 : ℤ) ^ (n - k) * (stirlingFirst n k : ℤ) : ℤ) : R) * X ^ k := by
  simpa only [Polynomial.map_prod, Polynomial.map_sub, map_X, map_C,
    Int.coe_castRingHom, Int.cast_natCast] using
    map_fallingFactorial_eq_sum (Int.castRingHom R) n

/-- Evaluation at any ring element, with the original integer coefficients. -/
theorem fallingFactorial_eval_eq_sum {R : Type*} [CommRing R] (n : ℕ) (x : R) :
    (∏ i ∈ Finset.range n, (x - (i : R))) =
      ∑ k ∈ Finset.range (n + 1),
        (((-1 : ℤ) ^ (n - k) * (stirlingFirst n k : ℤ) : ℤ) : R) * x ^ k := by
  have h := congrArg (Polynomial.eval x) (fallingFactorial_eq_sum_ring (R := R) n)
  simpa only [eval_prod, eval_sub, eval_X, eval_C, eval_finsetSum,
    eval_mul, eval_pow] using h

end FiniteCombinatorics.StirlingFallingExpansion
