import MathGenome.Internal.Specs.D07.Ch10.PrimeFactorizationUnique
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
Uniqueness of prime factorizations in an arbitrary domain. The library
lemma `prime_factors_unique` requires only a commutative monoid with zero
and cancellation of nonzero factors; it does not assume unique
factorization or existence of prime factorizations. Its induction matches
a prime with an associated prime on the other side and cancels it, exactly
as in paper.tex:1991–2004.
-/

universe u

namespace D07.Ch10.PrimeFactorizationUnique

open Specs.D07.Ch10.PrimeFactorizationUnique

/-- Matching prime factors, including their multiplicities and count. -/
theorem primeProductsUnique : PrimeProductsUnique.{u} := by
  intro R _ _ f g hf hg h
  have hrel : Multiset.Rel Associated f g := prime_factors_unique hf hg h
  exact ⟨Multiset.card_eq_card_of_rel hrel, hrel⟩

/-- Remove the leading units by association and apply prime-product uniqueness. -/
theorem primeFactorizationsUnique : PrimeFactorizationsUnique.{u} := by
  intro R _ _ f g u v hf hg h
  apply primeProductsUnique R f g hf hg
  exact (associated_unit_mul_right f.prod (u : R) u.isUnit).trans
    ((Associated.of_eq h).trans
      (associated_unit_mul_left g.prod (v : R) v.isUnit))

end D07.Ch10.PrimeFactorizationUnique
