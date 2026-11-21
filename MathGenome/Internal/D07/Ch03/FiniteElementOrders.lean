import MathGenome.Internal.D07.Ch02.CyclicModelsIsomorphism
import MathGenome.Internal.D07.Ch02.OrderDivisibility
import MathGenome.Internal.D07.Ch03.Lagrange
import MathGenome.Internal.Specs.D07.Ch03.FiniteElementOrders

/-! Orders in finite groups and the cyclic model for a group of prime order. -/

namespace D07.Ch03.FiniteElementOrders

universe u

theorem order_positive (G : Type u) [Group G] [Finite G] (x : G) :
    0 < orderOf x :=
  orderOf_pos x

theorem order_divides_card (G : Type u) [Group G] [Finite G] (x : G) :
    orderOf x ∣ Nat.card G := by
  -- The generated subgroup has cardinality equal to the element's order.
  rw [← Nat.card_zpowers]
  exact Lagrange.subgroup_card_divides G (Subgroup.zpowers x)

theorem power_card_eq_one (G : Type u) [Group G] [Finite G] (x : G) :
    x ^ Nat.card G = 1 := by
  obtain ⟨n, hn⟩ := order_divides_card G x
  rw [hn, pow_mul, pow_orderOf_eq_one, one_pow]

theorem prime_nonidentity_order (G : Type u) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (hcard : Nat.card G = p) (x : G) (hx : x ≠ 1) :
    orderOf x = p := by
  have hdiv : orderOf x ∣ p := hcard ▸ order_divides_card G x
  rcases hp.eq_one_or_self_of_dvd (orderOf x) hdiv with horder | horder
  · exact False.elim (hx (orderOf_eq_one_iff.mp horder))
  · exact horder

theorem prime_nonidentity_generates (G : Type u) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (hcard : Nat.card G = p) (x : G) (hx : x ≠ 1) :
    Subgroup.zpowers x = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_zpowers, prime_nonidentity_order G p hp hcard x hx, hcard]

theorem prime_isomorphic_cyclic_model (G : Type u) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (hcard : Nat.card G = p) :
    Nonempty (G ≃* Multiplicative (ZMod p)) := by
  have : Nontrivial G :=
    Finite.one_lt_card_iff_nontrivial.mp (hcard ▸ hp.one_lt)
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  obtain ⟨_, _, e, _⟩ := D07.Ch02.CyclicModelsIsomorphism.finite_model G x p
    (prime_nonidentity_generates G p hp hcard x hx) hp.pos
    (prime_nonidentity_order G p hp hcard x hx)
  exact ⟨e.symm⟩

end D07.Ch03.FiniteElementOrders
