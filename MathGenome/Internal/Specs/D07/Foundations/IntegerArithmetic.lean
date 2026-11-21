import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Nat.Prime.Defs

/-!
Independent statements for `paper.tex:97–121` (foundations.tex,
Theorem `thm:integer-arithmetic`). Lists retain prime multiplicities, and
`List.Perm` expresses uniqueness up to order. All input integers and all
factors are in ℤ; positivity fixes their sign.
-/

namespace D07.Foundations.IntegerArithmetic

/-- A positive integer prime. On positive integers `natAbs` is just the
corresponding natural number, and `Nat.Prime` is ordinary primality. -/
def PositivePrime (p : ℤ) : Prop :=
  0 < p ∧ Nat.Prime p.natAbs

namespace Specs

/-- A positive gcd, its universal divisibility property, and a Bézout equation. -/
def PositiveGcdBezout : Prop :=
  ∀ a b : ℤ, a ≠ 0 ∨ b ≠ 0 →
    ∃ d : ℤ, 0 < d ∧ d ∣ a ∧ d ∣ b ∧
      (∀ c : ℤ, c ∣ a → c ∣ b → c ∣ d) ∧
      ∃ x y : ℤ, d = x * a + y * b

/-- The all-zero boundary uses the normalized integer gcd zero. -/
def GcdZero : Prop :=
  (Int.gcd 0 0 : ℤ) = 0

/-- Euclid's lemma for positive integer primes and arbitrary signed factors. -/
def PrimeDividesProduct : Prop :=
  ∀ p : ℤ, PositivePrime p →
    ∀ a b : ℤ, p ∣ a * b → p ∣ a ∨ p ∣ b

/-- Every positive integer is a finite product of positive primes, and any
other such factorization differs by a permutation (including repetitions). -/
def UniquePrimeFactorization : Prop :=
  ∀ n : ℤ, 0 < n →
    ∃ l : List ℤ, (∀ p ∈ l, PositivePrime p) ∧ l.prod = n ∧
      ∀ m : List ℤ, (∀ p ∈ m, PositivePrime p) → m.prod = n → m.Perm l

/-- One has precisely the empty prime factorization, and zero has none. -/
def FactorizationBoundaries : Prop :=
  (([] : List ℤ).prod = 1) ∧
    ∀ l : List ℤ, (∀ p ∈ l, PositivePrime p) →
      (l.prod = 1 ↔ l = []) ∧ l.prod ≠ 0

end Specs
end D07.Foundations.IntegerArithmetic
