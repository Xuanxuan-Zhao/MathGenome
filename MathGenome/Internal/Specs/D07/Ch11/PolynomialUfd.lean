import MathGenome.Internal.Specs.D07.Ch10.UfdDefinition
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic

/-!
Independent statements for K07.11.polynomial_ufd, paper.tex:2604–2658.

The coefficient ring is a commutative nontrivial domain. The canonical
`UniqueFactorizationMonoid` predicate has the source's factorization meaning
under these hypotheses, as specified in Ch10.UfdDefinition. `Polynomial` and
`MvPolynomial` are formal polynomials, not polynomial evaluation functions.
The finite-variable assertion includes an empty variable type.
-/

universe u v

namespace Specs.D07.Ch11.PolynomialUfd

def PolynomialUfdIff : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R],
    UniqueFactorizationMonoid R ↔ UniqueFactorizationMonoid (Polynomial R)

def FiniteVariablePolynomialUfd : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (σ : Type v) [Finite σ], UniqueFactorizationMonoid (MvPolynomial σ R)

end Specs.D07.Ch11.PolynomialUfd
