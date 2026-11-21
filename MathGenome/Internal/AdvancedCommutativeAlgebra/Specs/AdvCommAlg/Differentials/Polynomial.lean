import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Universal
import Mathlib.RingTheory.Kaehler.Polynomial

/-! Independent specifications for paper.tex, KD-07 (lines 227–238).
The index type is arbitrary, including empty types; the coefficient ring may
be the zero ring. The sum is over the finite set of variables of the polynomial.
-/
namespace Specs.AdvCommAlg.Differentials

universe u v
noncomputable section

def polynomialBasisType := ∀ (A : Type u) (ι : Type v) [CommRing A],
  Module.Basis ι (MvPolynomial ι A) (KaehlerDifferential A (MvPolynomial ι A))

def polynomialBasisValue : polynomialBasisType.{u,v} :=
  fun A ι _ => KaehlerDifferential.mvPolynomialBasis A ι

def polynomialBasisApply : Prop := ∀ (A : Type u) (ι : Type v) [CommRing A] (i : ι),
  polynomialBasisValue A ι i =
    KaehlerDifferential.D A (MvPolynomial ι A) (MvPolynomial.X i)

def polynomialFree : Prop := ∀ (A : Type u) (ι : Type v) [CommRing A],
  Module.Free (MvPolynomial ι A) (KaehlerDifferential A (MvPolynomial ι A))

def polynomialCoordinates : Prop := ∀ (A : Type u) (ι : Type v) [CommRing A]
    (f : MvPolynomial ι A) (i : ι),
  (polynomialBasisValue A ι).repr (KaehlerDifferential.D A (MvPolynomial ι A) f) i =
    MvPolynomial.pderiv i f

def polynomialPartialsOutsideVars : Prop :=
  ∀ (A : Type u) (ι : Type v) [CommRing A] (f : MvPolynomial ι A) (i : ι),
    i ∉ f.vars → MvPolynomial.pderiv i f = 0

def polynomialDifferentialExpansion : Prop :=
  ∀ (A : Type u) (ι : Type v) [CommRing A] (f : MvPolynomial ι A),
    KaehlerDifferential.D A (MvPolynomial ι A) f =
      ∑ i ∈ f.vars, MvPolynomial.pderiv i f •
        KaehlerDifferential.D A (MvPolynomial ι A) (MvPolynomial.X i)

def univariateDifferential : Prop := ∀ (A : Type u) [CommRing A] (f : Polynomial A),
  KaehlerDifferential.D A (Polynomial A) f =
    Polynomial.derivative f • KaehlerDifferential.D A (Polynomial A) Polynomial.X

def emptyPolynomialDifferentials : Prop :=
  ∀ (A : Type u) (ι : Type v) [CommRing A] [IsEmpty ι],
    Subsingleton (KaehlerDifferential A (MvPolynomial ι A))

end
end Specs.AdvCommAlg.Differentials
