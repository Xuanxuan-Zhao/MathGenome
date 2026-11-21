import MathGenome.Internal.Specs.D07.Ch10.PrimeIrreducible
import MathGenome.Internal.D07.Ch09.PrimeIdeal

/-! Prime and irreducible elements, with the nonzero principal-ideal criterion.
`Ideal.span` is the commutative ideal representation; the upstream theorem
`D07.Ch08.PrincipalDivisibility.commutativeSpanCompatibility` identifies it
with the two-sided span used earlier in the paper.
-/

universe u

namespace D07.Ch10.PrimeIrreducible

open Specs.D07.Ch10.PrimeIrreducible

theorem irreducibleCharacterization : IrreducibleCharacterization.{u} := by
  intro R _ _ p
  constructor
  · intro hp
    exact ⟨hp.ne_zero, hp.not_isUnit, fun _ _ hab => hp.isUnit_or_isUnit hab⟩
  · rintro ⟨_, hnonunit, hfactor⟩
    exact ⟨hnonunit, fun {a b} hab => hfactor a b hab⟩

theorem primeCharacterization : PrimeCharacterization.{u} := by
  intro R _ _ p
  rfl

theorem principalIdealPrimeCharacterization : PrincipalIdealPrimeCharacterization.{u} := by
  intro R _ _ p
  rw [D07.Ch09.PrimeIdeal.primeCharacterization R (Ideal.span {p})]
  simp only [ne_eq, Ideal.span_singleton_eq_top, Ideal.mem_span_singleton]

theorem primeIffNonzeroPrimePrincipalIdeal : PrimeIffNonzeroPrimePrincipalIdeal.{u} := by
  intro R _ _ p
  rw [primeCharacterization R p, principalIdealPrimeCharacterization R p]

theorem zeroBoundary : ZeroBoundary.{u} := by
  intro R _ _
  refine ⟨not_prime_zero, not_irreducible_zero, Ideal.span_singleton_zero, ?_⟩
  rw [Ideal.span_singleton_zero]
  exact Ideal.isPrime_bot

end D07.Ch10.PrimeIrreducible
