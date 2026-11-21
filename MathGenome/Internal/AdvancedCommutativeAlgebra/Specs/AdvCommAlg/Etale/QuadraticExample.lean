import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Definitions
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! ET-16: the quadratic example, paper.tex:1970–1971.
All commutative rings, including the zero ring, are allowed. -/
namespace Specs.AdvCommAlg.Etale

universe u

/-- The literal polynomial quotient A[X]/(X²-a). -/
abbrev QuadraticQuotient (A : Type u) [CommRing A] (a : A) :=
  Polynomial A ⧸ Ideal.span {Polynomial.X ^ 2 - Polynomial.C a}

/-- The defining relation for the class of X. -/
def quadraticRootRelation : Prop := ∀ (A : Type u) [CommRing A] (a : A),
  (Ideal.Quotient.mk (Ideal.span {Polynomial.X ^ 2 - Polynomial.C a})
    Polynomial.X) ^ 2 = algebraMap A (QuadraticQuotient A a) a

/-- Invertibility of the derivative follows from the two stated unit assumptions. -/
def quadraticDerivativeUnit : Prop := ∀ (A : Type u) [CommRing A] (a : A),
  IsUnit (2 : A) → IsUnit a →
  IsUnit (Ideal.Quotient.mk (Ideal.span {Polynomial.X ^ 2 - Polynomial.C a})
    (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C a)))

/-- Étaleness for the specified base map, without a square root in A. -/
def quadraticEtale : Prop := ∀ (A : Type u) [CommRing A] (a : A),
  IsUnit (2 : A) → IsUnit a → etaleValue A (QuadraticQuotient A a)

end Specs.AdvCommAlg.Etale
