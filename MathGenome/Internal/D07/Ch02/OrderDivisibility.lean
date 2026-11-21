import MathGenome.Internal.D07.Ch02.ElementOrder
import MathGenome.Internal.Specs.D07.Ch02.OrderDivisibility

/-!
# When powers agree

All three assertions of `K07.02.order_divisibility`, for arbitrary groups.
The library divisibility laws apply even when `orderOf x = 0`; in that
case integer divisibility by zero reduces to equality of exponents.
-/

namespace D07.Ch02.OrderDivisibility

universe u

theorem finite_power_eq_one_iff (G : Type u) [Group G] (x : G) (n : ℕ)
    (_hn : 0 < n) (horder : orderOf x = n) (k : ℤ) :
    x ^ k = 1 ↔ (n : ℤ) ∣ k := by
  rw [← horder]
  exact orderOf_dvd_iff_zpow_eq_one.symm

theorem finite_powers_eq_iff (G : Type u) [Group G] (x : G) (n : ℕ)
    (_hn : 0 < n) (horder : orderOf x = n) (a b : ℤ) :
    x ^ a = x ^ b ↔ (n : ℤ) ∣ a - b := by
  rw [← horder]
  exact orderOf_dvd_sub_iff_zpow_eq_zpow.symm

theorem infinite_powers_eq_iff (G : Type u) [Group G] (x : G)
    (horder : orderOf x = 0) (a b : ℤ) :
    x ^ a = x ^ b ↔ a = b := by
  rw [← orderOf_dvd_sub_iff_zpow_eq_zpow, horder, Nat.cast_zero,
    zero_dvd_iff, sub_eq_zero]

end D07.Ch02.OrderDivisibility
