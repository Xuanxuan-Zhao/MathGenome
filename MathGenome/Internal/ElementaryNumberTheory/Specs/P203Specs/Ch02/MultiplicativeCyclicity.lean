import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.TotientClassicalCongruences
import Mathlib.Algebra.Field.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

/-! Independent statements for the cyclicity and generator-count portion of
paper.tex:447–508 (Theorem 2.3). The field need not be finite in the subgroup
statement. Generators are elements whose integer powers fill the group.
The totient is the source's unit-group cardinality, shared with Theorem 2.1.
No nontriviality condition is imposed on the groups, so order one is included.
-/

namespace P203Specs.Ch02

universe u

def FiniteMultiplicativeSubgroupCyclic : Prop :=
  ∀ (K : Type u) [Field K] (H : Subgroup Kˣ) [Finite H], IsCyclic H

def CyclicGeneratorCount : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [IsCyclic G] (d : ℕ),
    0 < d → Nat.card G = d →
    Nat.card {g : G // Subgroup.zpowers g = ⊤} = totient d

/-- The natural-exponent form of the order formula, including exponent zero. -/
def OrderOfNaturalPower : Prop :=
  ∀ (G : Type u) [Group G] (g : G) (d : ℕ),
    0 < d → orderOf g = d → ∀ j : ℕ,
    orderOf (g ^ j) = d / Nat.gcd d j

/-- For signed exponents gcd(d,j) is gcd(d,|j|). Only the element,
not the ambient group, is required to have finite positive order. -/
def OrderOfIntegerPower : Prop :=
  ∀ (G : Type u) [Group G] (g : G) (d : ℕ),
    0 < d → orderOf g = d → ∀ j : ℤ,
    orderOf (g ^ j) = d / Nat.gcd d j.natAbs

def PowerGeneratorCriterion : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (g : G) (d : ℕ),
    Subgroup.zpowers g = ⊤ → 0 < d → Nat.card G = d → ∀ j : ℤ,
    Subgroup.zpowers (g ^ j) = ⊤ ↔ Nat.gcd d j.natAbs = 1

/-- The units are those of the given field, rather than a chosen model of
a field of the same cardinality. This includes q = 2 and its sole generator. -/
def FiniteFieldMultiplicativeGroup : Prop :=
  ∀ (K : Type u) [Field K] [Finite K] (q : ℕ), Nat.card K = q →
    IsCyclic Kˣ ∧ Nat.card Kˣ = q - 1 ∧
    Nat.card {g : Kˣ // Subgroup.zpowers g = ⊤} = totient (q - 1)

end P203Specs.Ch02
