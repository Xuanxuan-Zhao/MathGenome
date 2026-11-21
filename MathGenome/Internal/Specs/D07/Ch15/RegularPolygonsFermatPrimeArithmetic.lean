import Mathlib.Data.Nat.Totient

/-!
Arithmetic statements for K07.15.regular_polygons, paper.tex:4568–4585.
`Nat.totient` counts coprime residue representatives. A finite set of prime
values encodes distinct factors; its empty product is permitted. All exponents
are natural numbers, so a power of two includes 1. In the exponent lemma,
positivity is necessary: exponent zero gives the even prime 2. The source
applies the lemma to odd primes, for which the exponent is positive.
-/

namespace Specs.D07.Ch15.RegularPolygonsFermatPrimeArithmetic

open scoped BigOperators

/-- The prime-power formula, in both the multiplicative and counting forms. -/
def TotientPrimePower : Prop :=
  ∀ p e : ℕ, p.Prime → 0 < e →
    Nat.totient (p ^ e) = p ^ (e - 1) * (p - 1) ∧
    Nat.totient (p ^ e) = p ^ e - p ^ (e - 1)

/-- The CRT product formula for arbitrary positive integers. -/
def TotientFactorization : Prop :=
  ∀ n : ℕ, n ≠ 0 →
    Nat.totient n = ∏ p ∈ n.primeFactors,
      p ^ (n.factorization p - 1) * (p - 1)

/-- The exponent in an odd prime one more than a power of two is a power of two. -/
def PrimeTwoPowerAddOne : Prop :=
  ∀ c : ℕ, 0 < c → Nat.Prime (1 + 2 ^ c) → ∃ b : ℕ, c = 2 ^ b

/-- The complete arithmetic equivalence in the Gauss–Wantzel criterion.
There is no bound on b or on the set of Fermat primes. -/
def TotientPowerTwoIff : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    ((∃ k : ℕ, Nat.totient n = 2 ^ k) ↔
    ∃ (a : ℕ) (s : Finset ℕ),
      n = 2 ^ a * ∏ p ∈ s, p ∧
      ∀ p ∈ s, Nat.Prime p ∧ Odd p ∧ ∃ b : ℕ, p = 1 + 2 ^ (2 ^ b))

end Specs.D07.Ch15.RegularPolygonsFermatPrimeArithmetic
