import MathGenome.Internal.Specs.D07.Ch10.UfdPrimeIrreducible
import MathGenome.Internal.D07.Ch10.UfdDefinition
import MathGenome.Internal.D07.Ch10.PrimeImpliesIrreducible

/-! Irreducible elements are prime in a UFD, K07.10.ufd_prime_irreducible.
The factorization proof does not assume `UniqueFactorizationMonoid`:
units supply empty multisets, and uniqueness pairs the irreducible with
a factor of one of the two multiplicands. The library theorem used below
handles zero multiplicands separately. The upstream characterization then
connects these hypotheses to the canonical UFD predicate.
-/

universe u

namespace D07.Ch10.UfdPrimeIrreducible

open Specs.D07.Ch10.UfdPrimeIrreducible

theorem irreducibleIsPrimeOfFactorizations : IrreducibleIsPrimeOfFactorizations.{u} := by
  intro R _ _ hex huniq p hp
  apply (irreducible_iff_prime_of_existsUnique_irreducible_factors ?_ huniq p).mp hp
  intro a ha
  by_cases hu : IsUnit a
  · refine ⟨0, fun b hb => (Multiset.notMem_zero b hb).elim, ?_⟩
    simpa only [Multiset.prod_zero] using (associated_one_iff_isUnit.mpr hu).symm
  · obtain ⟨s, _, hs, heq⟩ := hex a ha hu
    exact ⟨s, hs, Associated.of_eq heq⟩

theorem irreducibleIsPrime : IrreducibleIsPrime.{u} := by
  intro R _ _ _ p hp
  obtain ⟨hex, huniq⟩ := (D07.Ch10.UfdDefinition.ufdCharacterization R).mp inferInstance
  exact irreducibleIsPrimeOfFactorizations R hex huniq p hp

theorem primeIffIrreducible : PrimeIffIrreducible.{u} := by
  intro R _ _ _ p
  exact ⟨D07.Ch10.PrimeImpliesIrreducible.primeImpliesIrreducible R p,
    irreducibleIsPrime R p⟩

end D07.Ch10.UfdPrimeIrreducible
