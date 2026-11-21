import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-! The isomorphism classes are a quotient of actual finite abelian groups,
not a set of proposed elementary-divisor lists. Partitions have positive parts.
The index of the product is exactly the prime divisors of the positive order.
-/
noncomputable section
namespace Specs.D07.Ch07.EnumerateAbelianGroups
open scoped BigOperators

/-- A bundled finite abelian group with the prescribed cardinality. -/
structure AbelianGroupOfOrder (n : ℕ) where
  Carrier : Type
  [group : AddCommGroup Carrier]
  [finite : Finite Carrier]
  card_eq : Nat.card Carrier = n

attribute [instance] AbelianGroupOfOrder.group AbelianGroupOfOrder.finite

/-- Abstract additive isomorphism, with no chosen generators or decomposition. -/
def groupSetoid (n : ℕ) : Setoid (AbelianGroupOfOrder n) where
  r G H := Nonempty (G.Carrier ≃+ H.Carrier)
  iseqv := ⟨fun _ => ⟨AddEquiv.refl _⟩,
    fun ⟨f⟩ => ⟨f.symm⟩, fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩⟩

abbrev IsomorphismTypes (n : ℕ) := Quotient (groupSetoid n)

/-- Independent partition choices at the primes of the order. -/
abbrev PartitionData (n : ℕ) :=
  (p : n.primeFactors) → Nat.Partition (n.factorization p.val)

/-- The ordinary partition number, including the unique partition of zero. -/
def partitionNumber (a : ℕ) : ℕ := Nat.card (Nat.Partition a)

/-- The classification bridge needed to count actual group types. -/
def PartitionClassification : Prop :=
  ∀ n : ℕ, 0 < n → Nonempty (IsomorphismTypes n ≃ PartitionData n)

def EnumerationFormula : Prop :=
  ∀ n : ℕ, 0 < n →
    Nat.card (IsomorphismTypes n) =
      ∏ p ∈ n.primeFactors, partitionNumber (n.factorization p)

def FiniteTypes : Prop :=
  ∀ n : ℕ, 0 < n → Finite (IsomorphismTypes n)

/-- The empty prime product counts the zero group once. -/
def BoundaryCases : Prop :=
  partitionNumber 0 = 1 ∧ Nat.card (IsomorphismTypes 1) = 1

/-- Every finite abelian group, in any universe, has a representative in the
quotient's universe. Thus the chosen encoding does not restrict applicability. -/
def RepresentsAll.{u} : Prop :=
  ∀ (A : Type u) [AddCommGroup A] [Finite A] (n : ℕ),
    Nat.card A = n →
    ∃ G : AbelianGroupOfOrder n, Nonempty (A ≃+ G.Carrier)

end Specs.D07.Ch07.EnumerateAbelianGroups
