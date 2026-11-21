import Mathlib.Algebra.Prime.Defs
import Mathlib.Algebra.Ring.Defs

/-!
Independent specification for K07.10.prime_implies_irreducible
(paper.tex:1853–1862). The chapter's domain convention is commutative
and nontrivial. `Prime` excludes zero and units, and `Irreducible`
is the canonical nonunit factorization predicate; in a domain it also
excludes zero, as established in the upstream characterization.
-/

universe u

namespace Specs.D07.Ch10.PrimeImpliesIrreducible

/-- Every prime element of a commutative nontrivial domain is irreducible. -/
def PrimeIsIrreducible : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (p : R),
    Prime p → Irreducible p

end Specs.D07.Ch10.PrimeImpliesIrreducible
