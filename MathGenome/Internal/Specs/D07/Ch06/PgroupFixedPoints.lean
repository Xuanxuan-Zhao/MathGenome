import MathGenome.Internal.Specs.D07.Ch06.PgroupDefinition

/-!
Independent statements for `K07.06.pgroup_fixed_points`
(`paper.tex:973–983`). The finite p-group hypothesis is the upstream
cardinality definition, which includes finiteness and allows exponent zero.
Primality is explicit. The finite acted-on type may be empty.

The subtype below spells out the source's `X^G`: its members are fixed by
every group element, without any faithfulness or transitivity assumption.
-/

namespace Specs.D07.Ch06.PgroupFixedPoints

universe u v

/-- The cardinality of X is congruent to the number of global fixed points. -/
def CardModEqCardFixedPoints : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Finite X]
    (p : ℕ), p.Prime →
    Specs.D07.Ch06.PgroupDefinition.finitePGroupValue p G →
    Nat.ModEq p (Nat.card X) (Nat.card {x : X // ∀ g : G, g • x = x})

/-- If p does not divide the cardinality of X, there is a global fixed point. -/
def ExistsFixedPointOfNotDvdCard : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Finite X]
    (p : ℕ), p.Prime →
    Specs.D07.Ch06.PgroupDefinition.finitePGroupValue p G →
    ¬p ∣ Nat.card X → ∃ x : X, ∀ g : G, g • x = x

end Specs.D07.Ch06.PgroupFixedPoints
