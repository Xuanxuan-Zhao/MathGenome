import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.CubicDiscriminant

open Polynomial

namespace Specs.GaloisFormalization.IG.GenericCubic

/-- The family with parameter `a` in the coefficient ring. The generic parameter is
`RatFunc.X`, while `Polynomial.X` in this definition is the variable of the cubic. -/
noncomputable def polynomial {R : Type*} [CommRing R] (a : R) : R[X] :=
  X ^ 3 - X - C a

def polynomialDefinitionType := ∀ {R : Type*} [CommRing R], R → R[X]

def monicDegreeType : Prop :=
  ∀ {R : Type*} [CommRing R] [Nontrivial R] (a : R),
    (polynomial a).Monic ∧ (polynomial a).degree = 3

def mapType : Prop :=
  ∀ {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a : R),
    (polynomial a).map f = polynomial (f a)

def discriminantType : Prop :=
  ∀ {R : Type*} [CommRing R] [Nontrivial R] (a : R),
    (polynomial a).discr = 4 - 27 * a ^ 2

/-- Identification with the coefficient record used by Mathlib's cubic root formula. -/
def cubicType : Prop :=
  ∀ {R : Type*} [CommRing R] [Nontrivial R] (a : R),
    (⟨1, 0, -1, -a⟩ : Cubic R).toPoly = polynomial a ∧
      (⟨1, 0, -1, -a⟩ : Cubic R).discr = (polynomial a).discr

def irreducibleType : Prop :=
  ∀ (K : Type*) [Field K], Irreducible (polynomial (RatFunc.X : RatFunc K))

def separableType : Prop :=
  ∀ (K : Type*) [Field K] [CharZero K], (polynomial (RatFunc.X : RatFunc K)).Separable

def nonsquareType : Prop :=
  ∀ (K : Type*) [Field K] [CharZero K] [IsAlgClosed K],
    ¬ IsSquare (polynomial (RatFunc.X : RatFunc K)).discr

def geometricType : Prop :=
  let t : RatFunc (AlgebraicClosure ℚ) := RatFunc.X
  (polynomial t).Monic ∧ Irreducible (polynomial t) ∧ (polynomial t).Separable ∧
    (polynomial t).discr = 4 - 27 * t ^ 2 ∧ ¬ IsSquare (polynomial t).discr

def arithmeticDiscriminantType : Prop :=
  let t : RatFunc ℚ := RatFunc.X
  (polynomial t).discr = 4 - 27 * t ^ 2

/-- The family over the coefficient polynomial ring gives the generic cubic by localization. -/
def genericCoefficientsType : Prop :=
  ∀ (K : Type*) [Field K],
    (polynomial (X : K[X])).map (algebraMap K[X] (RatFunc K)) =
      polynomial (RatFunc.X : RatFunc K)

/-- Specialization evaluates the polynomial coefficients before passing to a function field. -/
def specializationType : Prop :=
  ∀ {K : Type*} [Field K] (a : K),
    let f := (polynomial (X : K[X])).map (evalRingHom a)
    f = polynomial a ∧ f.discr = 4 - 27 * a ^ 2

end Specs.GaloisFormalization.IG.GenericCubic
