import MathGenome.Internal.Specs.D07.Ch06.PgroupDefinition
import MathGenome.Internal.D07.Ch03.FiniteElementOrders

/-!
Finite prime-power groups (`K07.06.pgroup_definition`, paper.tex:962–971).

The finite-cardinality definition is kept separate from the potentially
infinite elementwise predicate `IsPGroup`. Mathlib's `IsPGroup.iff_card`
has precisely the finite and prime hypotheses needed for the converse;
its proof uses Cauchy's theorem and prime factorization. The forward
annihilation statement uses the accepted finite-element-order result.
-/

namespace D07.Ch06.PgroupDefinition

universe u

/-- For prime p, a finite p-group has p-power order, including p^0 = 1. -/
def FinitePGroup (p : ℕ) (G : Type u) [Group G] : Prop :=
  Specs.D07.Ch06.PgroupDefinition.finitePGroupValue p G

theorem finitePGroup_iff_card (G : Type u) [Group G] [Finite G] (p : ℕ) :
    FinitePGroup p G ↔ ∃ a : ℕ, Nat.card G = p ^ a :=
  ⟨And.right, fun h => ⟨inferInstance, h⟩⟩

theorem trivial_group_included (G : Type u) [Group G] [Subsingleton G]
    (p : ℕ) (_hp : p.Prime) :
    Nat.card G = p ^ 0 ∧ FinitePGroup p G := by
  have hcard : Nat.card G = p ^ 0 := by simp
  exact ⟨hcard, inferInstance, 0, hcard⟩

theorem power_prime_power_eq_one (G : Type u) [Group G] [Finite G]
    (p a : ℕ) (hcard : Nat.card G = p ^ a) (g : G) :
    g ^ (p ^ a) = 1 := by
  rw [← hcard]
  exact D07.Ch03.FiniteElementOrders.power_card_eq_one G g

theorem card_iff_elementwise (G : Type u) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) :
    (∃ a : ℕ, Nat.card G = p ^ a) ↔ ∀ g : G, ∃ k : ℕ, g ^ (p ^ k) = 1 := by
  constructor
  · rintro ⟨a, ha⟩ g
    exact ⟨a, power_prime_power_eq_one G p a ha g⟩
  · intro h
    let : Fact p.Prime := ⟨hp⟩
    exact IsPGroup.iff_card.mp h

theorem finitePGroup_iff_finite_isPGroup (G : Type u) [Group G]
    (p : ℕ) (hp : p.Prime) :
    FinitePGroup p G ↔ Finite G ∧ IsPGroup p G := by
  constructor
  · rintro ⟨hfinite, hcard⟩
    let : Finite G := hfinite
    exact ⟨hfinite, (card_iff_elementwise G p hp).mp hcard⟩
  · rintro ⟨hfinite, h⟩
    let : Finite G := hfinite
    exact ⟨hfinite, (card_iff_elementwise G p hp).mpr h⟩

end D07.Ch06.PgroupDefinition
