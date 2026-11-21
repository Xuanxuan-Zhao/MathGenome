import MathGenome.Internal.Specs.D07.Ch18.NilpotenceCriteria

/-!
Independent specification of K07.18.pgroup_nilpotent, paper.tex:5053–5071.
The cardinality is the order of an explicitly finite group. Primality is
explicit, and the exponent ranges over all natural numbers, including zero.
Both bounds use the canonical upper-series termination predicate. Exact
classes use its least termination length, with no fallback for nonnilpotent
groups. In particular the sharper bound is restricted to exponents at least 2.
-/

namespace Specs.D07.Ch18.PgroupNilpotent

open Specs.D07.Ch18.NilpotenceCriteria

universe u

def ClassAtMostExponent : Prop :=
  ∀ (P : Type u) [Group P] [Finite P] (p a : ℕ), p.Prime →
    Nat.card P = p ^ a → classAtMostValue P a

def SharperClassBound : Prop :=
  ∀ (P : Type u) [Group P] [Finite P] (p a : ℕ), p.Prime →
    Nat.card P = p ^ a → 2 ≤ a → classAtMostValue P (a - 1)

def PrimeOrderClassOne : Prop :=
  ∀ (P : Type u) [Group P] [Finite P] (p : ℕ), p.Prime →
    Nat.card P = p ^ 1 → hasClassValue P 1

def ExponentZeroClassZero : Prop :=
  ∀ (P : Type u) [Group P] [Finite P] (p : ℕ), p.Prime →
    Nat.card P = p ^ 0 → hasClassValue P 0

def PrimePowerNilpotent : Prop :=
  ∀ (P : Type u) [Group P] [Finite P] (p a : ℕ), p.Prime →
    Nat.card P = p ^ a → Group.IsNilpotent P

end Specs.D07.Ch18.PgroupNilpotent
