import MathGenome.Internal.Specs.D07.Ch01.ArithmeticExamples
import MathGenome.Internal.Specs.D07.Ch02.CyclicDefinition
import MathGenome.Internal.Specs.D07.Ch02.OrderDivisibility
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.SetTheory.Cardinal.Defs

/-!
Independent statements for `K07.02.cyclic_models_isomorphism`
(paper.tex:445–451; chapters/M07.02.tex:23–29).

`Multiplicative` only changes notation: the model operation is addition on
the integers or on the canonical residue group `ZMod n`. The isomorphisms
below send the integer (or residue class) `k` to the indicated generator's
`k`th power. Generation means that the canonical integer-power subgroup is
the entire given group, with no added commutativity assumption.

The finite model includes `n = 1`. Infinite order is `orderOf x = 0` and
has an explicitly infinite carrier. Classification records finite groups
of equal finite size or two infinite groups, so infinity is never inferred
from an unqualified equality of natural cardinalities.
-/

namespace Specs.D07.Ch02.CyclicModelsIsomorphism

universe u v

/-- The infinite model, including the formula for its isomorphism. -/
def InfiniteModel : Prop :=
  ∀ (G : Type u) [Group G] (x : G),
    Subgroup.zpowers x = ⊤ → orderOf x = 0 →
      Infinite G ∧ ∃ e : Multiplicative ℤ ≃* G,
        ∀ k : ℤ, e (Multiplicative.ofAdd k) = x ^ k

/-- The finite model and its cardinality, for every positive order. -/
def FiniteModel : Prop :=
  ∀ (G : Type u) [Group G] (x : G) (n : ℕ),
    Subgroup.zpowers x = ⊤ → 0 < n → orderOf x = n →
      Finite G ∧ Nat.card G = n ∧
        ∃ e : Multiplicative (ZMod n) ≃* G,
          ∀ k : ℤ, e (Multiplicative.ofAdd (k : ZMod n)) = x ^ k

/-- Full classification, with finite and infinite group orders distinguished.
The two groups may live in different universes. -/
def IsomorphicIffSameOrder : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] [IsCyclic G] [IsCyclic H],
    Nonempty (G ≃* H) ↔
      (Finite G ∧ Finite H ∧ Nat.card G = Nat.card H) ∨
        (Infinite G ∧ Infinite H)

/-- The same classification stated using actual set cardinalities.
Lifts allow arbitrary universes without replacing infinity by a natural zero. -/
def IsomorphicIffSameCardinality : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] [IsCyclic G] [IsCyclic H],
    Nonempty (G ≃* H) ↔
      Cardinal.lift.{v} (Cardinal.mk G) = Cardinal.lift.{u} (Cardinal.mk H)

end Specs.D07.Ch02.CyclicModelsIsomorphism
