import MathGenome.Internal.Specs.D07.Ch11.FactorRemainder
import MathGenome.Internal.D07.Ch10.PrimeImpliesIrreducible
import Mathlib.Algebra.Polynomial.RingDivision

/-!
The factor and remainder theorems, K07.11.factor_remainder.

Monic division gives the remainder C(f(a)) over any commutative ring,
including the zero ring. The root-factor equivalence has the same scope.
In a domain the linear factor is prime; applying the upstream theorem
that prime elements are irreducible gives the last assertion.
-/

universe u

namespace D07.Ch11.FactorRemainder

open Polynomial
open Specs.D07.Ch11.FactorRemainder

theorem remainder_formula : RemainderFormula.{u} := by
  intro R _ f a
  exact Polynomial.modByMonic_X_sub_C_eq_C_eval f a

theorem factor_iff : FactorIff.{u} := by
  intro R _ f a
  exact (Polynomial.dvd_iff_isRoot).symm

theorem linear_prime : LinearPrime.{u} := by
  intro R _ _ a
  exact Polynomial.prime_X_sub_C a

theorem linear_irreducible : LinearIrreducible.{u} := by
  intro R _ _ a
  exact D07.Ch10.PrimeImpliesIrreducible.primeImpliesIrreducible
    (Polynomial R) (X - C a) (linear_prime R a)

end D07.Ch11.FactorRemainder
