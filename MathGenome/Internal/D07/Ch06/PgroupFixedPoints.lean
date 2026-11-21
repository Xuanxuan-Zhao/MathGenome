import MathGenome.Internal.Specs.D07.Ch06.PgroupFixedPoints
import MathGenome.Internal.D07.Ch06.PgroupDefinition

/-!
The fixed-point congruence and its existence consequence
(`K07.06.pgroup_fixed_points`, paper.tex:973–983).

The upstream finite-cardinality/elementwise equivalence supplies Mathlib's
`IsPGroup` hypothesis. Mathlib proves the congruence by partitioning X into
orbits of p-power size: singleton orbits correspond exactly to global fixed
points, and the other orbits contribute zero modulo p. Its fixed-point
existence theorem is the consequent of this congruence when p ∤ |X|.
-/

namespace D07.Ch06.PgroupFixedPoints

universe u v

open D07.Ch06.PgroupDefinition

theorem card_modEq_card_fixedPoints (G : Type u) (X : Type v)
    [Group G] [MulAction G X] [Finite X] (p : ℕ) (hp : p.Prime)
    (hG : FinitePGroup p G) :
    Nat.ModEq p (Nat.card X) (Nat.card {x : X // ∀ g : G, g • x = x}) := by
  let : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p G :=
    ((finitePGroup_iff_finite_isPGroup G p hp).mp hG).2
  exact hpg.card_modEq_card_fixedPoints X

theorem exists_fixed_point_of_not_dvd_card (G : Type u) (X : Type v)
    [Group G] [MulAction G X] [Finite X] (p : ℕ) (hp : p.Prime)
    (hG : FinitePGroup p G) (hcard : ¬p ∣ Nat.card X) :
    ∃ x : X, ∀ g : G, g • x = x := by
  let : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p G :=
    ((finitePGroup_iff_finite_isPGroup G p hp).mp hG).2
  exact hpg.nonempty_fixed_point_of_prime_not_dvd_card X hcard

end D07.Ch06.PgroupFixedPoints
