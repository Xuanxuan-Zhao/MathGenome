import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch01.FactorizationValuations
import Mathlib.Algebra.Ring.Parity

/-!
The existence and odd-prime clauses of Theorem 4.4 (`nt:D04`) of
`paper.tex`, lines 1525–1529. Primes are positive rational primes,
represented by natural primes and cast to integers. Signed integer witnesses
are allowed, including zero coordinates. The finite valuation is the `toNat`
of the canonical extended valuation of Chapter 1; positivity excludes infinity.
The representation count and its zero case are assigned separately to D04Count.
-/
namespace P203Specs.Ch04

/-- Every prime congruent to three modulo four, including primes not dividing
`n`, has even finite valuation precisely when `n` is a sum of two squares. -/
def TwoSquaresCriterion : Prop :=
  ∀ n : ℤ, 0 < n →
    ((∃ a b : ℤ, n = a ^ 2 + b ^ 2) ↔
      ∀ p : ℕ, p.Prime → p % 4 = 3 →
        Even ((Ch01.primeValuation p n).toNat))

/-- The odd-prime specialization, for all positive rational primes. -/
def OddPrimeTwoSquares : Prop :=
  ∀ p : ℕ, p.Prime → Odd p →
    ((∃ a b : ℤ, (p : ℤ) = a ^ 2 + b ^ 2) ↔ p % 4 = 1)

end P203Specs.Ch04
