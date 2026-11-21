import MathGenome.Internal.Specs.D05.M10.ComplexSquareRoots
import MathGenome.Internal.D05.M08.Evaluation
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.Polynomial.Div

/-! The nilpotent polynomial square-root lemma. Formal binomial convolution is
used solely to establish a finite coefficient identity: no analytic series is
evaluated, and the final substitution is of a polynomial in K[X]. -/

noncomputable section

namespace D05.M10.ComplexSquareRoots

open Polynomial

/-- Explicit finite polynomial, with coefficients binomial(1/2,k). -/
def rootPolynomial : Specs.D05.M10.ComplexSquareRoots.rootPolynomial_type :=
  Specs.D05.M10.ComplexSquareRoots.rootPolynomial_value

variable {K : Type*} [Field K] [CharZero K]

/-- Auxiliary representation for checking the finite coefficients. -/
theorem rootPolynomial_eq_trunc (r : ℕ) :
    rootPolynomial K r = PowerSeries.trunc r (PowerSeries.binomialSeries K (1 / 2 : ℚ)) := by
  simp [rootPolynomial, Specs.D05.M10.ComplexSquareRoots.rootPolynomial_value,
    PowerSeries.trunc_apply, Nat.Ico_zero_eq_range, Algebra.smul_def]

/-- Vandermonde convolution at exponents 1/2 and 1/2. -/
private theorem binomial_half_square :
    (PowerSeries.binomialSeries K (1 / 2 : ℚ)) ^ 2 = 1 + PowerSeries.X := by
  rw [pow_two, ← PowerSeries.binomialSeries_add]
  norm_num
  simpa using (PowerSeries.binomialSeries_nat (R := ℚ) (A := K) 1)

theorem polynomial_congruence : Specs.D05.M10.ComplexSquareRoots.polynomial_congruence := by
  intro K _ _ r
  change (X : Polynomial K) ^ r ∣ rootPolynomial K r ^ 2 - (1 + X)
  rw [X_pow_dvd_iff]
  intro d hd
  rw [coeff_sub, sub_eq_zero, rootPolynomial_eq_trunc]
  have h := PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc
    (PowerSeries.binomialSeries K (1 / 2 : ℚ))
    (PowerSeries.binomialSeries K (1 / 2 : ℚ)) hd
  simpa only [← pow_two, binomial_half_square, map_add, ← Polynomial.coe_pow, Polynomial.coeff_coe, coeff_add,
    PowerSeries.coeff_one, PowerSeries.coeff_X, Polynomial.coeff_one,
    Polynomial.coeff_X, eq_comm] using h.symm

theorem polynomial_square_root : Specs.D05.M10.ComplexSquareRoots.polynomial_square_root := by
  intro K V _ _ _ _ Q r _hr hQ
  have h := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero
    (polynomial_congruence K r) (by simpa using hQ : aeval Q ((X : Polynomial K) ^ r) = 0)
  simpa only [map_sub, map_pow, map_add, map_one, aeval_X, sub_eq_zero] using h

theorem exists_polynomial_square_root :
    Specs.D05.M10.ComplexSquareRoots.exists_polynomial_square_root := by
  intro K V _ _ _ _ Q r hr hQ
  refine ⟨rootPolynomial K r, ?_, polynomial_square_root K V Q r hr hQ⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  rw [rootPolynomial_eq_trunc]
  exact PowerSeries.natDegree_trunc_lt _ n

end D05.M10.ComplexSquareRoots
