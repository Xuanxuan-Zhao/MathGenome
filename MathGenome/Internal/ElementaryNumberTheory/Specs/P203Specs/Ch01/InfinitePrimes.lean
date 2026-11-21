import Mathlib.Data.Nat.PrimeFin

/-!
Independent statements of `paper.tex`, Theorem 1.7 (lines 323–347).
As in the Chapter 1 factorization specification, positive integer primes
are represented by natural numbers `p` satisfying `p.Prime`.
The remainder condition `p % 4 = 3` is ordinary congruence modulo 4.
The finite-set clauses include the empty set without an extra hypothesis.
-/
namespace P203Specs.Ch01

def InfinitePrimes : Prop :=
  {p : ℕ | p.Prime}.Infinite ∧
    ∀ s : Finset ℕ, ∃ p : ℕ, p.Prime ∧ p ∉ s

def InfinitePrimesThreeModFour : Prop :=
  {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite ∧
    ∀ s : Finset ℕ, ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ p ∉ s

end P203Specs.Ch01
