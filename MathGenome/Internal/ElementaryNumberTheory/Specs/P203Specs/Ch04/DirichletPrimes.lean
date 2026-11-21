import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Defs

namespace P203Specs.Ch04

/-- Theorem 4.8 (`nt:dirichlet-primes`), paper.tex:1691–1695.
The modulus is a positive natural number and the residue is an arbitrary integer.
Primes are positive integers, represented by naturals; congruence is divisibility
of the difference, as in the source's global conventions. -/
def DirichletPrimes : Prop :=
  ∀ (M : ℕ), 1 ≤ M → ∀ (a : ℤ), Int.gcd a (M : ℤ) = 1 →
    ∀ (T : ℝ), ∃ q : ℕ,
      0 < q ∧ q.Prime ∧ T < (q : ℝ) ∧ (M : ℤ) ∣ (q : ℤ) - a

end P203Specs.Ch04
