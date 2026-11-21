import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Rat.Defs

/-!
Independent statements for K07.13.irreducible_count, paper.tex:3998–4018.
The coefficient field K is fixed and q is its actual cardinality. No choice
of an isomorphic finite-field copy is involved. The count is a natural
cardinality of precisely the monic irreducibles of the specified degree;
its finiteness is an explicit obligation. The second identity is in ℚ,
so the division is rational division, including its signed Möbius terms.
`ArithmeticFunction.moebius` is 1 at 1, (-1) to the number of prime factors
on squarefree integers, and zero on integers divisible by a prime square.
-/

universe u
namespace Specs.D07.Ch13.IrreducibleCount

open Polynomial

/-- Number of monic irreducibles of degree n over the given base field. -/
noncomputable def count (K : Type u) [Field K] (n : ℕ) : ℕ :=
  Nat.card {f : K[X] // f.Monic ∧ Irreducible f ∧ f.natDegree = n}

def FiniteCounts : Prop :=
  ∀ (K : Type u) [Field K] [Finite K] (n : ℕ), 1 ≤ n →
    Finite {f : K[X] // f.Monic ∧ Irreducible f ∧ f.natDegree = n}

def DegreeSum : Prop :=
  ∀ (K : Type u) [Field K] [Finite K] (q n : ℕ),
    Nat.card K = q → 1 ≤ n →
      q ^ n = ∑ d ∈ n.divisors, d * count K d

def MobiusFormula : Prop :=
  ∀ (K : Type u) [Field K] [Finite K] (q n : ℕ),
    Nat.card K = q → 1 ≤ n →
      (count K n : ℚ) = (1 / (n : ℚ)) *
        ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℚ) * (q : ℚ) ^ (n / d)

end Specs.D07.Ch13.IrreducibleCount
