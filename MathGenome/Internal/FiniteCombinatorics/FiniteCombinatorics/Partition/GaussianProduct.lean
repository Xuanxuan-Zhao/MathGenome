import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Partition.RectangularPartitions
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Partition.GaussianProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
namespace FiniteCombinatorics.Partition

open GaussianProductSpecs

@[simp] theorem polynomialImage_X :
    polynomialImage Polynomial.X = (RatFunc.X : RatFunc ℚ) := by
  simp [polynomialImage]

/-- The finite product of the first `m` cyclotomic factors (without splitting
those factors into irreducibles). -/
def qFactorial (m : ℕ) : RatFunc ℚ :=
  ∏ i ∈ Finset.range m, (1 - (RatFunc.X : RatFunc ℚ) ^ (i + 1))

@[simp] theorem qFactorial_zero : qFactorial 0 = 1 := by
  simp [qFactorial]

theorem qFactorial_succ (m : ℕ) :
    qFactorial (m + 1) = qFactorial m * (1 - RatFunc.X ^ (m + 1)) := by
  exact Finset.prod_range_succ _ _

theorem one_sub_X_pow_ne_zero {m : ℕ} (hm : 0 < m) :
    (1 - (RatFunc.X : RatFunc ℚ) ^ m) ≠ 0 := by
  have hp : (1 - (Polynomial.X : Polynomial ℚ) ^ m) ≠ 0 := by
    intro h
    have hc := congrArg (fun p : Polynomial ℚ => p.coeff 0) h
    simp [Polynomial.coeff_X_pow, (Nat.ne_of_gt hm).symm] at hc
  have h := RatFunc.algebraMap_ne_zero (K := ℚ) hp
  simpa using h

theorem qFactorial_ne_zero (m : ℕ) : qFactorial m ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact one_sub_X_pow_ne_zero (Nat.succ_pos i)

/-- The rational factorial expression satisfies the same rectangular recurrence. -/
theorem rectangle_factorial (a b : ℕ) :
    polynomialImage (F a b) = qFactorial (a + b) /
      (qFactorial a * qFactorial b) := by
  induction a generalizing b with
  | zero => simp [qFactorial_ne_zero]
  | succ a iha =>
    induction b with
    | zero => simp [qFactorial_ne_zero]
    | succ b ihb =>
      rw [F_succ_succ, map_add, map_mul, map_pow, polynomialImage_X, ihb, iha]
      have hn : a + 1 + (b + 1) = (a + b + 1) + 1 := by omega
      have hn' : a + 1 + b = a + b + 1 := by omega
      rw [hn, hn', qFactorial_succ (a + b + 1), qFactorial_succ a,
        qFactorial_succ b]
      have he : a + b + 1 + 1 = (a + 1) + (b + 1) := by omega
      rw [he, pow_add RatFunc.X (a + 1) (b + 1)]
      field_simp [qFactorial_ne_zero, one_sub_X_pow_ne_zero (Nat.succ_pos a),
        one_sub_X_pow_ne_zero (Nat.succ_pos b)]
      ring

/-- Splitting the finite product at `b` gives the shifted numerator factors. -/
theorem qFactorial_add (a b : ℕ) :
    qFactorial (a + b) = qFactorial b *
      ∏ i ∈ Finset.range a, (1 - (RatFunc.X : RatFunc ℚ) ^ (b + (i + 1))) := by
  simpa only [qFactorial, Nat.add_assoc, Nat.add_comm a b] using
    (Finset.prod_range_add
      (fun i => 1 - (RatFunc.X : RatFunc ℚ) ^ (i + 1)) b a)

/-- Product formula directly for the actual rectangular partition polynomial. -/
theorem rectangle_product (a b : ℕ) :
    polynomialImage (F a b) =
      ∏ i ∈ Finset.range a,
        (1 - (RatFunc.X : RatFunc ℚ) ^ (b + (i + 1))) /
          (1 - (RatFunc.X : RatFunc ℚ) ^ (i + 1)) := by
  rw [rectangle_factorial, qFactorial_add, Finset.prod_div_distrib]
  change qFactorial b * _ / (qFactorial a * qFactorial b) = _ / qFactorial a
  field_simp [qFactorial_ne_zero]

/-- W28: the Gaussian weight polynomial equals the quotient in ℚ(q),
including `k = 0`, `k = n`, and `n = 0`. -/
theorem gaussian_product : GaussianProductSpecs.ProductFormula := by
  intro n k hk
  change polynomialImage (if k ≤ n then F k (n - k) else 0) = _
  rw [ite_eq_left hk]
  exact rectangle_product k (n - k)

end FiniteCombinatorics.Partition
