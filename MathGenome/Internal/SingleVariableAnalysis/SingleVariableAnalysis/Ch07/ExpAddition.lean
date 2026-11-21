import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.ExpConstruction
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.CauchyProduct
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.ExpAddition
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp

/-!
# Addition law for the factorial-series exponential

K03.07.exp_addition, paper.tex:1561–1579. The finite binomial identity
identifies the Cauchy-product coefficients. Mertens' theorem and uniqueness
of the ordinary series sum then give the addition law for the shared series
construction. The zero value is computed from the series; nonvanishing and
the reciprocal formula follow by setting the second argument to -z.
-/

noncomputable section
namespace SingleVariableAnalysis
open scoped BigOperators

namespace ExpAddition

/-- The binomial theorem identifies each coefficient of the Cauchy product. -/
theorem cauchyProduct_term (z w : ℂ) (n : ℕ) :
    complexCauchyProduct (fun k => z^k / (k.factorial : ℂ))
      (fun k => w^k / (k.factorial : ℂ)) n = (z + w)^n / (n.factorial : ℂ) := by
  unfold complexCauchyProduct
  rw [add_pow, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [Nat.cast_choose ℂ hkn]
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hkf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hnk : ((n-k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n-k))
  field_simp

end ExpAddition

theorem expSeries_add (z w : ℂ) : seriesExp (z + w) = seriesExp z * seriesExp w := by
  have hp := complex_mertens
    (fun n => z^n / (n.factorial : ℂ)) (fun n => w^n / (n.factorial : ℂ))
    (seriesExp z) (seriesExp w) (expSeries_absolute z) (expSeries_hasSum z) (expSeries_hasSum w)
  have he : complexCauchyProduct (fun n => z^n / (n.factorial : ℂ))
      (fun n => w^n / (n.factorial : ℂ)) =
      (fun n => (z+w)^n / (n.factorial : ℂ)) :=
    funext (ExpAddition.cauchyProduct_term z w)
  rw [he] at hp
  exact complex_series_sum_unique _ _ _ (expSeries_hasSum (z+w)) hp

theorem expSeries_zero : seriesExp 0 = 1 := by
  change (∑' n : ℕ, (0 : ℂ)^n / (n.factorial : ℂ)) = 1
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

theorem expSeries_ne_zero (z : ℂ) : seriesExp z ≠ 0 := by
  intro hz
  have h := expSeries_add z (-z)
  rw [add_neg_cancel, expSeries_zero, hz, zero_mul] at h
  exact one_ne_zero h

theorem expSeries_neg (z : ℂ) : seriesExp (-z) = 1 / seriesExp z := by
  apply (eq_div_iff (expSeries_ne_zero z)).mpr
  rw [mul_comm, ← expSeries_add, add_neg_cancel, expSeries_zero]

end SingleVariableAnalysis
