import MathGenome.Internal.Specs.D07.Ch09.PrimeQuotient
import MathGenome.Internal.D07.Ch09.QuotientTrivial
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
K07.09.prime_quotient: prime quotients and the zero-ideal corollary.
The library quotient criterion translates properness to nontriviality
and the prime product condition to absence of zero divisors. For the
corollary, the upstream zero-ideal quotient equivalence identifies the
quotient domain condition with the domain condition on the original ring.
-/

universe u

namespace D07.Ch09.PrimeQuotient

open Specs.D07.Ch09.PrimeQuotient

theorem prime_iff_quotient_domain : PrimeIffQuotientDomain.{u} := by
  intro R _ P
  exact (Ideal.Quotient.isDomain_iff_prime P).symm

theorem domain_iff_bot_prime : DomainIffBotPrime.{u} := by
  intro R _
  obtain ⟨e, _, _⟩ :=
    D07.Ch09.QuotientTrivial.zero_ideal_quotient_equivalence R
  exact e.toMulEquiv.isDomain_iff.symm.trans
    (prime_iff_quotient_domain R (⊥ : Ideal R)).symm

end D07.Ch09.PrimeQuotient
