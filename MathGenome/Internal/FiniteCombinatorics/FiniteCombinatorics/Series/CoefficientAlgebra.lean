import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.CoefficientAlgebra
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Series.GeneratingSeries
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-! Products and formal differentiation, paper.tex, p204:W11. -/

noncomputable section

universe u

namespace FiniteCombinatorics.Series

open scoped BigOperators

/-- The coefficient of a product is its finite Cauchy convolution. -/
theorem coeff_mul {R : Type u} [CommRing R] (A B : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (A * B) =
      ∑ i ∈ Finset.range (n + 1),
        PowerSeries.coeff i A * PowerSeries.coeff (n - i) B := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- Formal differentiation multiplies the shifted coefficient by its degree. -/
theorem coeff_derivative {R : Type u} [CommRing R] (A : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.derivative A) =
      (n + 1 : R) * PowerSeries.coeff (n + 1) A := by
  rw [PowerSeries.coeff_derivative, mul_comm]

/-- The formal product rule over a commutative ring. -/
theorem derivative_mul {R : Type u} [CommRing R] (A B : PowerSeries R) :
    PowerSeries.derivative (A * B) =
      PowerSeries.derivative A * B + A * PowerSeries.derivative B := by
  simpa only [smul_eq_mul, mul_comm, add_comm] using
    (PowerSeries.derivative (R := R)).leibniz A B

/-- A constant series has zero formal derivative. -/
theorem derivative_C {R : Type u} [CommRing R] (r : R) :
    PowerSeries.derivative (PowerSeries.C r) = 0 :=
  PowerSeries.derivative_C

/-- Cauchy convolution for the OGF of arbitrary sequences. -/
theorem coeff_mul_ogf {R : Type u} [CommRing R] (a b : ℕ → R) (n : ℕ) :
    PowerSeries.coeff n (ogf a * ogf b) =
      ∑ i ∈ Finset.range (n + 1), a i * b (n - i) := by
  simp only [coeff_mul, coeff_ogf]

/-- The coefficient formula for the derivative of an OGF. -/
theorem coeff_derivative_ogf {R : Type u} [CommRing R] (a : ℕ → R) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.derivative (ogf a)) =
      (n + 1 : R) * a (n + 1) := by
  rw [coeff_derivative, coeff_ogf]

/-- The rational factorial identity underlying exponential convolution. -/
private theorem reciprocal_factorial_mul (n i : ℕ) (hi : i ≤ n) :
    (i.factorial : ℚ)⁻¹ * ((n - i).factorial : ℚ)⁻¹ =
      (Nat.choose n i : ℚ) * (n.factorial : ℚ)⁻¹ := by
  have h : (Nat.choose n i : ℚ) * (i.factorial : ℚ) *
      ((n - i).factorial : ℚ) = (n.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have hi0 : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hj0 : ((n - i).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - i)
  have hn0 : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h.symm

/-- Multiplication of EGFs gives the EGF of the binomial convolution. -/
theorem egf_mul {R : Type u} [CommRing R] [Algebra ℚ R] (a b : ℕ → R) :
    egf a * egf b =
      egf (fun n => ∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : R) * a i * b (n - i)) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_mul, coeff_egf, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coeff_egf, coeff_egf]
  have h := congrArg (algebraMap ℚ R)
    (reciprocal_factorial_mul n i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
  simp only [map_mul, map_natCast] at h
  calc
    _ = (a i * b (n - i)) *
        (algebraMap ℚ R ((i.factorial : ℚ)⁻¹) *
          algebraMap ℚ R (((n - i).factorial : ℚ)⁻¹)) := by ring
    _ = _ := by rw [h]; ring

end FiniteCombinatorics.Series
