import MathGenome.Internal.Specs.D07.Ch07.CardinalityExponentRankMinimumGenerators
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Fintype.BigOperators

/-! Independent statements for K07.07.cardinality_exponent_rank,
`paper.tex:3485–3494`. The normalized product and its normalization predicate
are the same objects as in the minimum-generator prerequisite. The canonical
additive exponent is explicitly characterized as the least positive annihilator.
The empty product is included in every universal statement. -/
namespace Specs.D07.Ch07.CardinalityExponentRank

open Specs.D07.Ch07.CardinalityExponentRankMinimumGenerators

/-- The order is the product of the actual cyclic orders. -/
def Order : Prop :=
  ∀ (r : ℕ) (d : Fin r → ℕ), Normalized d →
    Nat.card (CyclicProduct d) = ∏ i, d i

/-- In a nonempty chain the last order is the exponent. -/
def NonemptyExponent : Prop :=
  ∀ (r : ℕ) (d : Fin (r + 1) → ℕ), Normalized d →
    AddMonoid.exponent (CyclicProduct d) = d (Fin.last r)

def EmptyExponent : Prop :=
  ∀ d : Fin 0 → ℕ, AddMonoid.exponent (CyclicProduct d) = 1

/-- No extra annihilation or positivity premise is imposed on the group. -/
def LeastPositiveExponent : Prop :=
  ∀ (r : ℕ) (d : Fin r → ℕ), Normalized d →
    IsLeast {n : ℕ | 0 < n ∧ ∀ x : CyclicProduct d, n • x = 0}
      (AddMonoid.exponent (CyclicProduct d))

/-- Both existence and minimality of a generating set of size `r`. -/
def MinimumGenerators : Prop :=
  Specs.D07.Ch07.CardinalityExponentRankMinimumGenerators.MinimumGenerators

def CyclicIffRank : Prop :=
  ∀ (r : ℕ) (d : Fin r → ℕ), Normalized d →
    (IsAddCyclic (CyclicProduct d) ↔ r ≤ 1)

def CyclicIffExponentOrder : Prop :=
  ∀ (r : ℕ) (d : Fin r → ℕ), Normalized d →
    (IsAddCyclic (CyclicProduct d) ↔
      AddMonoid.exponent (CyclicProduct d) = Nat.card (CyclicProduct d))

end Specs.D07.Ch07.CardinalityExponentRank
