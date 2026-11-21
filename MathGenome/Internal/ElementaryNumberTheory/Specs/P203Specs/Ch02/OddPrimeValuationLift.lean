import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch01.FactorizationValuations

/-!
The valuation assertion of `paper.tex`, Theorem 2.4 (`nt:B03`, lines
509–527), with the valuation conventions of Theorem 1.3. A positive prime
integer is represented by a natural prime and its cast to the integers.
The integer `u` is unrestricted in sign. Congruence means divisibility of
the difference, as in the source's global conventions.
-/
namespace P203Specs.Ch02

open P203Specs.Ch01

/-- Both differences are nonzero, so the equality of canonical extended
valuations also gives the stated equality of their finite natural values. -/
def OddPrimeValuationLift : Prop :=
  ∀ p : ℕ, p.Prime → Odd p → ∀ u : ℤ,
    (p : ℤ) ∣ u - 1 → u ≠ 1 →
    u - 1 ≠ 0 ∧ u ^ p - 1 ≠ 0 ∧
    primeValuation p (u ^ p - 1) = primeValuation p (u - 1) + 1 ∧
    (primeValuation p (u ^ p - 1)).toNat =
      (primeValuation p (u - 1)).toNat + 1

end P203Specs.Ch02
