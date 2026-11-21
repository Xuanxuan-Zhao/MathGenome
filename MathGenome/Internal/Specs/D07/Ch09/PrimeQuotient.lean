import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
Independent statements for K07.09.prime_quotient, paper.tex:1648–1658.
The source has restricted to commutative unital rings. The zero ring and
the whole ideal remain allowed as inputs: primality includes properness,
and `IsDomain` includes nontriviality. The quotient is the same canonical
additive-coset ring used by the upstream quotient construction.
-/

universe u

namespace Specs.D07.Ch09.PrimeQuotient

/-- An ideal is prime exactly when its quotient is an integral domain.
No properness or nontriviality is assumed in advance. -/
def PrimeIffQuotientDomain : Prop :=
  ∀ (R : Type u) [CommRing R] (P : Ideal R),
    P.IsPrime ↔ IsDomain (R ⧸ P)

/-- The zero-ideal specialization, stated for the original ring itself. -/
def DomainIffBotPrime : Prop :=
  ∀ (R : Type u) [CommRing R],
    IsDomain R ↔ (⊥ : Ideal R).IsPrime

end Specs.D07.Ch09.PrimeQuotient
