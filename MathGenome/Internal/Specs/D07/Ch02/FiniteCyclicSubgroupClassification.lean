import MathGenome.Internal.Specs.D07.Ch02.CyclicAbelianAndSubgroups
import MathGenome.Internal.Specs.D07.Ch02.CyclicModelsIsomorphism
import MathGenome.Internal.Specs.D07.Ch02.OrderOfPower
import Mathlib.Data.Nat.Totient

/-!
Independent statements of `K07.02.finite_cyclic_subgroup_classification`
(paper.tex:481–488; chapters/M07.02.tex:59–66).

Generation uses the same canonical integer-power subgroup as Chapter 2.
The positive natural cardinality assumption expresses that the group has
finite order n, without an additional commutativity or nontriviality premise.
For each positive divisor, we specify both the size of the indicated subgroup
and its equality with every subgroup of that size. Exponents in the generator
criterion range over all integers; their gcd with n is expressed using natAbs.
The counted subtype consists of elements, not integer exponents or subgroups.
All statements include n = 1, and the divisor statement includes d = 1 and d = n.
-/

namespace Specs.D07.Ch02.FiniteCyclicSubgroupClassification

universe u

/-- The specified subgroup exists and is the unique subgroup of divisor order. -/
def UniqueSubgroupOfOrder : Prop :=
  ∀ (G : Type u) [Group G] (x : G) (n : ℕ),
    Subgroup.zpowers x = ⊤ → 0 < n → Nat.card G = n →
      ∀ d : ℕ, 0 < d → d ∣ n →
        Nat.card (Subgroup.zpowers (x ^ (n / d))) = d ∧
          ∀ H : Subgroup G,
            Nat.card H = d ↔ H = Subgroup.zpowers (x ^ (n / d))

/-- Integer powers generate exactly for exponents relatively prime to n. -/
def PowerGeneratesIff : Prop :=
  ∀ (G : Type u) [Group G] (x : G) (n : ℕ),
    Subgroup.zpowers x = ⊤ → 0 < n → Nat.card G = n →
      ∀ k : ℤ, Subgroup.zpowers (x ^ k) = ⊤ ↔ Nat.gcd k.natAbs n = 1

/-- Exactly totient n elements of the group generate it, including for n = 1. -/
def GeneratorCount : Prop :=
  ∀ (G : Type u) [Group G] (x : G) (n : ℕ),
    Subgroup.zpowers x = ⊤ → 0 < n → Nat.card G = n →
      Nat.card {y : G // Subgroup.zpowers y = ⊤} = Nat.totient n

end Specs.D07.Ch02.FiniteCyclicSubgroupClassification
