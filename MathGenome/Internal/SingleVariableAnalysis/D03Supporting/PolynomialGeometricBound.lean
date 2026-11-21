import MathGenome.Internal.SingleVariableAnalysis.Specs.D03Supporting.PolynomialGeometricBound
import MathGenome.Internal.SingleVariableAnalysis.D03Supporting.BinomialCoefficientLowerBound
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace D03Supporting

/-- Quantitative polynomial versus geometric bounds, including the threshold. -/
theorem explicit_polynomial_geometric_bound :
    Specs.D03Supporting.PolynomialGeometricBound := by
  intro k n r hr
  dsimp only
  intro hn
  have hd : 0 < r - 1 := sub_pos.mpr hr
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hnp : 0 < n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnp
  have hfpos : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
  have hrpow : 0 < r ^ n := pow_pos hrpos _
  have hdpow : 0 < (r - 1) ^ (k + 1) := pow_pos hd _
  have htwo : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  have hbinom : (Nat.choose n (k + 1) : ℝ) * (r - 1) ^ (k + 1) ≤ r ^ n := by
    have hsum := Finset.single_le_sum
      (s := Finset.range (n + 1))
      (f := fun i => (r - 1) ^ i * (1 : ℝ) ^ (n - i) * (Nat.choose n i : ℝ))
      (a := k + 1)
      (fun i _ => by positivity)
      (show k + 1 ∈ Finset.range (n + 1) by simp only [Finset.mem_range]; omega)
    calc
      (Nat.choose n (k + 1) : ℝ) * (r - 1) ^ (k + 1) =
          (r - 1) ^ (k + 1) * (1 : ℝ) ^ (n - (k + 1)) *
            (Nat.choose n (k + 1) : ℝ) := by simp [mul_comm]
      _ ≤ ∑ i ∈ Finset.range (n + 1),
          (r - 1) ^ i * (1 : ℝ) ^ (n - i) * (Nat.choose n i : ℝ) := hsum
      _ = (r - 1 + 1) ^ n := (add_pow (r - 1) (1 : ℝ) n).symm
      _ = r ^ n := by ring_nf
  have hcoefficient := binomial_coefficient_lower_bound (k + 1) n (by omega) hn
  have hsecond :
      (((n : ℝ) / 2) ^ (k + 1) * (r - 1) ^ (k + 1)) /
          ((k + 1).factorial : ℝ) ≤
        (Nat.choose n (k + 1) : ℝ) * (r - 1) ^ (k + 1) := by
    simpa only [div_mul_eq_mul_div] using
      mul_le_mul_of_nonneg_right hcoefficient hdpow.le
  refine ⟨hbinom, hsecond, div_nonneg (by positivity) hrpow.le, ?_⟩
  have hlower := le_trans hsecond hbinom
  rw [div_le_iff₀ hfpos, div_pow, div_mul_eq_mul_div, div_le_iff₀ htwo] at hlower
  apply (div_le_div_iff₀ hrpow (mul_pos hdpow hnpos)).mpr
  calc
    (n : ℝ) ^ k * ((r - 1) ^ (k + 1) * (n : ℝ)) =
        (n : ℝ) ^ (k + 1) * (r - 1) ^ (k + 1) := by rw [pow_succ]; ring
    _ ≤ (r ^ n * ((k + 1).factorial : ℝ)) * 2 ^ (k + 1) := hlower
    _ = (2 ^ (k + 1) * ((k + 1).factorial : ℝ)) * r ^ n := by ring

end D03Supporting
