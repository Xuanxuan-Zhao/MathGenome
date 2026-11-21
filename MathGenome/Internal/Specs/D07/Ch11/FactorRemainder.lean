import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Prime.Defs

/-!
Independent specification of K07.11.factor_remainder
(paper.tex:2388–2408; chapters/M07.11.tex:243–263).

`Polynomial R` is the formal polynomial ring used by the upstream entries.
The remainder is the canonical remainder for monic division (`%ₘ`), not
field division. The remainder and factor formulas allow every commutative
unital ring, including the zero ring. Only the prime and irreducible
conclusions require a domain, which includes nontriviality.
-/

universe u

namespace Specs.D07.Ch11.FactorRemainder

open Polynomial

/-- The remainder upon division by the monic linear polynomial is evaluation,
viewed as a constant formal polynomial. -/
def RemainderFormula : Prop :=
  ∀ (R : Type u) [CommRing R] (f : Polynomial R) (a : R),
    f %ₘ (X - C a) = C (f.eval a)

/-- A root is equivalent to divisibility by its monic linear factor. -/
def FactorIff : Prop :=
  ∀ (R : Type u) [CommRing R] (f : Polynomial R) (a : R),
    f.eval a = 0 ↔ X - C a ∣ f

/-- Over a domain, every monic linear polynomial X-C(a) is prime. -/
def LinearPrime : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a : R),
    Prime (X - C a : Polynomial R)

/-- Over a domain, every monic linear polynomial X-C(a) is irreducible. -/
def LinearIrreducible : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a : R),
    Irreducible (X - C a : Polynomial R)

end Specs.D07.Ch11.FactorRemainder
