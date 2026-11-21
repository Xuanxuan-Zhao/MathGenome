import Mathlib.GroupTheory.PGroup

/-!
Independent definitions and statements for `K07.06.pgroup_definition`
(`paper.tex:962–971`). For prime `p`, the source's finite p-group has
cardinality `p ^ a` for a natural exponent `a`, including zero.

The cardinality predicate below includes finiteness as a conjunct. Thus a
natural cardinality is never used to count an infinite group. Primality is
an explicit hypothesis of the characterization theorems. In contrast,
Mathlib's `IsPGroup` is the elementwise annihilation predicate, with no
finiteness built into its definition.
-/

namespace Specs.D07.Ch06.PgroupDefinition

universe u

abbrev FinitePGroupPredicateType :=
  (p : ℕ) → (G : Type u) → [Group G] → Prop

/-- On prime inputs, this is the source's definition of a finite p-group. -/
def finitePGroupValue : FinitePGroupPredicateType.{u} :=
  fun p G _ => Finite G ∧ ∃ a : ℕ, Nat.card G = p ^ a

/-- With finiteness supplied, the definition is exactly p-power order. -/
def FinitePGroupIffCard : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p : ℕ),
    finitePGroupValue p G ↔ ∃ a : ℕ, Nat.card G = p ^ a

/-- Every trivial group has exponent-zero cardinality and is included. -/
def TrivialGroupIncluded : Prop :=
  ∀ (G : Type u) [Group G] [Subsingleton G] (p : ℕ),
    p.Prime → Nat.card G = p ^ 0 ∧ finitePGroupValue p G

/-- The group order p^a annihilates each element. -/
def PowerPrimePowerEqOne : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p a : ℕ),
    Nat.card G = p ^ a → ∀ g : G, g ^ (p ^ a) = 1

/-- The full cardinality/elementwise equivalence in the proposition. -/
def CardIffElementwise : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p : ℕ), p.Prime →
    ((∃ a : ℕ, Nat.card G = p ^ a) ↔ ∀ g : G, ∃ k : ℕ, g ^ (p ^ k) = 1)

/-- The bridge to the library predicate keeps finiteness explicit even when
the ambient group has no supplied finite instance. -/
def FinitePGroupIffFiniteIsPGroup : Prop :=
  ∀ (G : Type u) [Group G] (p : ℕ), p.Prime →
    (finitePGroupValue p G ↔ Finite G ∧ IsPGroup p G)

end Specs.D07.Ch06.PgroupDefinition
