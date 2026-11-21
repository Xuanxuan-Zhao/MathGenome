import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
Independent statements for the unit-lifting step of
`paper.tex:1597` in K05.10.semisimple_decomposition.

The argument uses only the underlying commutative unital ring of the algebra.
Thus these statements apply in particular to every commutative unital algebra,
without any characteristic, finite-dimensionality, or nontriviality restriction.
`IsNilpotent J` means that some ordinary ideal power of `J` is zero.
All sums below are finite sums over `Finset.range r`, i.e. exponents 0 through r-1.
-/

namespace D05.Specs.M10.SemisimpleDecomposition.Units

/-- The displayed inverse formula. The ideal membership of z is unnecessary for
this algebraic identity once its vanishing power is given. -/
def finiteInverseFormula : Prop :=
  ∀ (R : Type*) [CommRing R] (u v z : R) (r : ℕ),
    1 ≤ r → u * v = 1 - z → z ^ r = 0 →
    u * (v * ∑ i ∈ Finset.range r, z ^ i) = 1 ∧
    (v * ∑ i ∈ Finset.range r, z ^ i) * u = 1

/-- A quotient unit supplies a representative inverse v and a nilpotent error z
in J, and the stated finite formula gives both inverse identities in R. -/
def liftUnitWithFormula : Prop :=
  ∀ (R : Type*) [CommRing R] (J : Ideal R),
    IsNilpotent J → ∀ u : R, IsUnit (Ideal.Quotient.mk J u) →
    ∃ (v z : R) (r : ℕ),
      1 ≤ r ∧ z ∈ J ∧ u * v = 1 - z ∧ z ^ r = 0 ∧
      u * (v * ∑ i ∈ Finset.range r, z ^ i) = 1 ∧
      (v * ∑ i ∈ Finset.range r, z ^ i) * u = 1

/-- Invertibility modulo a nilpotent ideal implies invertibility in the algebra. -/
def isUnitOfIsUnitQuotient : Prop :=
  ∀ (R : Type*) [CommRing R] (J : Ideal R),
    IsNilpotent J → ∀ u : R, IsUnit (Ideal.Quotient.mk J u) → IsUnit u

end D05.Specs.M10.SemisimpleDecomposition.Units
