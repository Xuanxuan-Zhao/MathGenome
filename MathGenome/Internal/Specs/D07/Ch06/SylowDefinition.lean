import MathGenome.Internal.Specs.D07.Ch06.PgroupDefinition
import Mathlib.GroupTheory.Sylow

/-!
Independent statements for `K07.06.sylow_definition`, paper.tex:1032–1039.
Maximality is among all finite p-subgroups, including the subgroup itself
and the whole group when it is a p-group. It is not maximality among
proper subgroups. No positivity assumption is imposed on the exponent.
-/

namespace Specs.D07.Ch06.SylowDefinition

universe u

/-- Membership in the family of finite p-subgroups, together with maximality
under inclusion in that family. -/
def maximalPSubgroup (p : ℕ) {G : Type u} [Group G] (P : Subgroup G) : Prop :=
  PgroupDefinition.finitePGroupValue p P ∧
    ∀ Q : Subgroup G,
      PgroupDefinition.finitePGroupValue p Q → P ≤ Q → Q = P

/-- The source's complete cardinality/maximality equivalence. -/
def MaximalIffCard : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p a m : ℕ),
    p.Prime → Nat.card G = p ^ a * m → ¬ p ∣ m →
    ∀ P : Subgroup G, maximalPSubgroup p P ↔ Nat.card P = p ^ a

/-- The same equivalence for the library's maximal-p-subgroup structure. -/
def SylowIffCard : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p a m : ℕ),
    p.Prime → Nat.card G = p ^ a * m → ¬ p ∣ m →
    ∀ P : Subgroup G,
      (∃ S : Sylow p G, S.toSubgroup = P) ↔ Nat.card P = p ^ a

/-- If p does not divide the group order, the trivial subgroup is the
unique maximal p-subgroup. -/
def MaximalIffBotOfNotDvdCard : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p : ℕ), p.Prime →
    ¬ p ∣ Nat.card G →
    ∀ P : Subgroup G, maximalPSubgroup p P ↔ P = ⊥

end Specs.D07.Ch06.SylowDefinition
