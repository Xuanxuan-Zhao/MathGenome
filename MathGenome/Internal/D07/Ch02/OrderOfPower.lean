import MathGenome.Internal.D07.Ch02.OrderDivisibility
import MathGenome.Internal.D07.Foundations.IntegerArithmetic
import MathGenome.Internal.Specs.D07.Ch02.OrderOfPower

/-!
# The order of a power

All conclusions of `K07.02.order_of_power` for arbitrary groups. The
finite-order formula includes the zero exponent. Infinite order is treated
separately, since the zero exponent then has order one rather than zero.
-/

namespace D07.Ch02.OrderOfPower

universe u

theorem finite_order_of_power (G : Type u) [Group G] (x : G) (n : ℕ)
    (hn : 0 < n) (horder : orderOf x = n) (k : ℤ) :
    orderOf (x ^ k) = n / Nat.gcd n k.natAbs := by
  have hx : IsOfFinOrder x := orderOf_pos_iff.mp (horder.symm ▸ hn)
  calc
    orderOf (x ^ k) = orderOf (x ^ k.natAbs) := (orderOf_pow_natAbs x k).symm
    _ = orderOf x / Nat.gcd (orderOf x) k.natAbs := hx.orderOf_pow x k.natAbs
    _ = n / Nat.gcd n k.natAbs := by rw [horder]

theorem infinite_order_zero_power (G : Type u) [Group G] (x : G)
    (_horder : orderOf x = 0) : orderOf (x ^ (0 : ℤ)) = 1 := by
  simp only [zpow_zero, orderOf_one]

theorem infinite_order_nonzero_power (G : Type u) [Group G] (x : G)
    (horder : orderOf x = 0) (k : ℤ) (hk : k ≠ 0) :
    orderOf (x ^ k) = 0 := by
  simpa only [horder, Nat.zero_div] using (orderOf_zpow' x hk)

end D07.Ch02.OrderOfPower
