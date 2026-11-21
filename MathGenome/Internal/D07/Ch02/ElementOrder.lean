import MathGenome.Internal.D07.Ch01.IntegerPowerLaws
import MathGenome.Internal.Specs.D07.Ch02.ElementOrder

/-!
# Finite and infinite element order

The definition and characterizations in `K07.02.element_order` for any
group, using Mathlib's canonical order with zero encoding infinity.
-/

namespace D07.Ch02.ElementOrder

universe u

/-- The least positive annihilating exponent, or zero for infinite order. -/
noncomputable abbrev elementOrder (G : Type u) [Group G] (x : G) : ℕ :=
  orderOf x

theorem finite_order_iff (G : Type u) [Group G] (x : G) :
    0 < elementOrder G x ↔ ∃ n : ℕ, 0 < n ∧ x ^ n = 1 :=
  orderOf_pos_iff.trans isOfFinOrder_iff_pow_eq_one

theorem least_positive_exponent (G : Type u) [Group G] (x : G) (n : ℕ)
    (hn : 0 < n) :
    elementOrder G x = n ↔
      x ^ n = 1 ∧ ∀ m : ℕ, 0 < m → x ^ m = 1 → n ≤ m := by
  constructor
  · intro h
    refine ⟨h ▸ pow_orderOf_eq_one x, ?_⟩
    intro m hm hpow
    exact h ▸ orderOf_le_of_pow_eq_one hm hpow
  · rintro ⟨hpow, hmin⟩
    have hpos : 0 < orderOf x :=
      (finite_order_iff G x).mpr ⟨n, hn, hpow⟩
    exact Nat.le_antisymm (orderOf_le_of_pow_eq_one hn hpow)
      (hmin (orderOf x) hpos (pow_orderOf_eq_one x))

theorem infinite_order_iff (G : Type u) [Group G] (x : G) :
    elementOrder G x = 0 ↔ ∀ n : ℕ, 0 < n → x ^ n ≠ 1 :=
  orderOf_eq_zero_iff'

theorem order_one_iff (G : Type u) [Group G] (x : G) :
    elementOrder G x = 1 ↔ x = 1 :=
  orderOf_eq_one_iff

end D07.Ch02.ElementOrder
