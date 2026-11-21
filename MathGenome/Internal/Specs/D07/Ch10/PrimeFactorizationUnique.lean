import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Prime.Defs
import Mathlib.Algebra.Ring.Defs

/-!
Independent specifications for `support.prime_factorization_unique`,
paper.tex:1986–2004 (lem:prime-factorization-unique).

The ambient ring is an arbitrary commutative nontrivial domain, with no
factorization-existence, PID, or UFD assumption. Multisets represent finite
factor lists modulo reordering and retain multiplicities. `Multiset.Rel
Associated f g` is a one-to-one matching of occurrences of factors, each
pair differing by multiplication by a unit. Thus it expresses precisely
uniqueness up to units and order, not just equality of sets of factors.
Empty multisets are allowed and have product one.
-/

universe u

namespace Specs.D07.Ch10.PrimeFactorizationUnique

/-- Associated products of primes have the same number of factors and a
matching of their factors up to units, retaining all multiplicities. -/
def PrimeProductsUnique : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (f g : Multiset R),
    (∀ p ∈ f, Prime p) → (∀ q ∈ g, Prime q) →
    Associated f.prod g.prod →
    f.card = g.card ∧ Multiset.Rel Associated f g

/-- The source's displayed equality, allowing arbitrary leading units on
both sides. This includes factorizations of units by empty products. -/
def PrimeFactorizationsUnique : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (f g : Multiset R) (u v : Rˣ),
    (∀ p ∈ f, Prime p) → (∀ q ∈ g, Prime q) →
    (u : R) * f.prod = (v : R) * g.prod →
    f.card = g.card ∧ Multiset.Rel Associated f g

end Specs.D07.Ch10.PrimeFactorizationUnique
