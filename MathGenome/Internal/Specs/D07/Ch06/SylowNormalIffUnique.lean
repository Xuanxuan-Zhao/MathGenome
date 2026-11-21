import MathGenome.Internal.Specs.D07.Ch06.SylowDefinition
import MathGenome.Internal.Specs.D07.Ch04.CharacteristicSubgroups

/-!
Independent statements for `K07.06.sylow_normal_iff_unique`, paper.tex:1060–1068.

`Sylow p G` consists of maximal p-subgroups. The upstream Sylow-definition
entry identifies these with subgroups of order p^a when |G| = p^a * m and
p does not divide m. Thus `Nat.card (Sylow p G)` counts exactly the source's
Sylow subgroups. Ambient finiteness and primality are explicit throughout.
The final two statements also give the conclusions directly for the source's
cardinality presentation. Exponent zero and the trivial group are allowed.
-/

namespace Specs.D07.Ch06.SylowNormalIffUnique

universe u

/-- Normality is equivalent to every Sylow subgroup being the given one. -/
def NormalIffUnique : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p : ℕ), p.Prime →
    ∀ P : Sylow p G,
      P.toSubgroup.Normal ↔ ∀ Q : Sylow p G, Q = P

/-- The number n_p of Sylow p-subgroups is one exactly in the normal case. -/
def NormalIffCountOne : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p : ℕ), p.Prime →
    ∀ P : Sylow p G,
      P.toSubgroup.Normal ↔ Nat.card (Sylow p G) = 1

/-- A normal Sylow subgroup is invariant under every automorphism. -/
def CharacteristicOfNormal : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p : ℕ), p.Prime →
    ∀ P : Sylow p G,
      P.toSubgroup.Normal → P.toSubgroup.Characteristic

/-- The normality/uniqueness equivalence using the largest p-power order. -/
def NormalIffUniqueOfCard : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p a m : ℕ),
    p.Prime → Nat.card G = p ^ a * m → ¬ p ∣ m →
    ∀ P : Subgroup G, Nat.card P = p ^ a →
      (P.Normal ↔ ∀ Q : Subgroup G, Nat.card Q = p ^ a → Q = P)

/-- Characteristicity using the largest p-power order. -/
def CharacteristicOfNormalOfCard : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p a m : ℕ),
    p.Prime → Nat.card G = p ^ a * m → ¬ p ∣ m →
    ∀ P : Subgroup G, Nat.card P = p ^ a → P.Normal → P.Characteristic

end Specs.D07.Ch06.SylowNormalIffUnique
