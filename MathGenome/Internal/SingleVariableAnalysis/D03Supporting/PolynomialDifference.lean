import MathGenome.Internal.SingleVariableAnalysis.Specs.D03Supporting.PolynomialDifference
import Mathlib.Algebra.Order.Ring.Abs

namespace D03Supporting

/-- Factorization bounds the difference of powers uniformly on `[0, r + 1]`. -/
theorem polynomial_difference_bound : Specs.PolynomialDifferenceBound := by
  intro m _hm r _hr u v hu hv
  have hmax : max |u| |v| ≤ r + 1 := by
    rw [abs_of_nonneg hu.1, abs_of_nonneg hv.1]
    exact max_le hu.2 hv.2
  have hpow : max |u| |v| ^ (m - 1) ≤ (r + 1) ^ (m - 1) :=
    pow_le_pow_left₀ ((abs_nonneg u).trans (le_max_left _ _)) hmax _
  calc
    |u ^ m - v ^ m| ≤ |u - v| * (m : ℝ) * max |u| |v| ^ (m - 1) :=
      abs_pow_sub_pow_le u v m
    _ ≤ |u - v| * (m : ℝ) * (r + 1) ^ (m - 1) :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    _ = (m : ℝ) * (r + 1) ^ (m - 1) * |u - v| := by
      ac_rfl

end D03Supporting
