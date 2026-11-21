import MathGenome.Internal.D07.Ch01.ElementaryGroupLaws
import MathGenome.Internal.Specs.D07.Ch01.IntegerPowerLaws
import Mathlib.Algebra.Group.Commute.Defs

/-!
# Powers with integer exponents

The conventions and all laws of `K07.01.integer_power_laws` for arbitrary
groups. The convention lemmas explicitly connect the canonical integer
power to finite repeated multiplication and to natural powers of inverses.
-/

namespace D07.Ch01.IntegerPowerLaws

universe u

theorem positive_power_product (G : Type u) [Group G] (x : G) (n : ℕ)
    (_hn : 0 < n) : x ^ (n : ℤ) = (List.replicate n x).prod :=
  (zpow_natCast x n).trans (List.prod_replicate n x).symm

theorem zero_power (G : Type u) [Group G] (x : G) : x ^ (0 : ℤ) = 1 :=
  zpow_zero x

theorem negative_natural_power (G : Type u) [Group G] (x : G) (n : ℕ) :
    x ^ (-(n : ℤ)) = (x⁻¹) ^ n := by
  rw [zpow_neg, zpow_natCast, inv_pow]

theorem power_add (G : Type u) [Group G] (x : G) (m n : ℤ) :
    x ^ (m + n) = x ^ m * x ^ n :=
  zpow_add x m n

theorem power_mul (G : Type u) [Group G] (x : G) (m n : ℤ) :
    (x ^ m) ^ n = x ^ (m * n) :=
  (zpow_mul x m n).symm

theorem power_neg (G : Type u) [Group G] (x : G) (n : ℤ) :
    x ^ (-n) = (x ^ n)⁻¹ :=
  zpow_neg x n

theorem commuting_product_power (G : Type u) [Group G] (x y : G)
    (h : x * y = y * x) (n : ℤ) : (x * y) ^ n = x ^ n * y ^ n :=
  (show Commute x y from h).mul_zpow n

end D07.Ch01.IntegerPowerLaws
