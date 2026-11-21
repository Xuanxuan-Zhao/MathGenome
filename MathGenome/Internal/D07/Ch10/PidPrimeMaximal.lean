import MathGenome.Internal.Specs.D07.Ch10.PidPrimeMaximal
import MathGenome.Internal.D07.Ch10.PidDefinition
import MathGenome.Internal.D07.Ch10.PrimeIrreducible
import MathGenome.Internal.D07.Ch10.PrimeImpliesIrreducible
import MathGenome.Internal.D07.Ch09.MaximalPrimeNonconverse
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
Primes, irreducibles and maximal ideals in a PID (K07.10.pid_prime_maximal).
The upstream PID characterization installs precisely the domain and principal
ideal hypotheses of the library results. Nonzero assumptions are retained on
both the prime-ideal theorem and the element equivalences.
-/

universe u

namespace D07.Ch10.PidPrimeMaximal

open Specs.D07.Ch10.PidPrimeMaximal

theorem nonzero_prime_ideal_maximal : NonzeroPrimeIdealMaximal.{u} := by
  intro R _ hPID I hI hprime
  obtain ⟨hDomain, hPrincipal⟩ := (PidDefinition.pid_iff R).mp hPID
  let := hDomain
  let := hPrincipal
  let := hprime
  exact IsPrime.to_maximal_ideal hI

theorem irreducible_iff_maximal : IrreducibleIffMaximal.{u} := by
  intro R _ hPID p hp
  obtain ⟨hDomain, hPrincipal⟩ := (PidDefinition.pid_iff R).mp hPID
  let := hDomain
  let := hPrincipal
  simpa only [Ideal.submodule_span_eq] using
    (Ideal.irreducible_iff_isMaximal_span_singleton hp)

theorem prime_iff_maximal : PrimeIffMaximal.{u} := by
  intro R _ hPID p hp
  let := hPID.1
  constructor
  · intro hprime
    have hspan : (Ideal.span {p}).IsPrime :=
      ((PrimeIrreducible.primeIffNonzeroPrimePrincipalIdeal R p).mp hprime).2
    exact nonzero_prime_ideal_maximal R hPID (Ideal.span {p})
      (fun h => hp (Ideal.span_singleton_eq_bot.mp h)) hspan
  · intro hmax
    exact (PrimeIrreducible.primeIffNonzeroPrimePrincipalIdeal R p).mpr
      ⟨hp, Ch09.MaximalPrimeNonconverse.maximal_implies_prime R _ hmax⟩

theorem irreducible_iff_prime : IrreducibleIffPrime.{u} := by
  intro R _ hPID p hp
  let := hPID.1
  constructor
  · intro hirred
    exact (prime_iff_maximal R hPID p hp).mpr
      ((irreducible_iff_maximal R hPID p hp).mp hirred)
  · exact PrimeImpliesIrreducible.primeImpliesIrreducible R p

theorem integer_zero_prime_not_maximal : IntegerZeroPrimeNotMaximal :=
  Ch09.MaximalPrimeNonconverse.integer_zero_prime_not_maximal

end D07.Ch10.PidPrimeMaximal
