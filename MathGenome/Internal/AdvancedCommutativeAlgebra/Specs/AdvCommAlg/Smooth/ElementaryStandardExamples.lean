import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.StandardPresentation

/-! SM-16, first two examples (paper.tex:1464–1469). The singleton
variable type `Unit` represents A[T]. Counts belong to the displayed
presentations; no nonzero hypothesis is imposed on A or its quotients. -/
namespace Specs.AdvCommAlg.Smooth.Elementary

universe u
noncomputable section
open MvPolynomial

/-- The literal quotient A[T]/(aT-1). -/
abbrev InverseQuotient (A : Type u) [CommRing A] (a : A) :=
  MvPolynomial Unit A ⧸ Ideal.span {C a * X () - 1}

/-- The polynomial presentation, with exactly n variables and no equations. -/
def polynomialPresentation (A : Type u) [CommRing A] (n : ℕ) :
    Algebra.Presentation A (MvPolynomial (Fin n) A) (Fin n) (Fin 0) :=
  (Algebra.Presentation.mvPolynomial.{0} A (Fin n)).reindex (Equiv.refl _) finZeroEquiv'

/-- The canonical localization presentation transported to the literal
quotient, and indexed by Fin 1 on both variables and equations. -/
def inversePresentation (A : Type u) [CommRing A] (a : A) :
    Algebra.Presentation A (InverseQuotient A a) (Fin 1) (Fin 1) :=
  ((Algebra.Presentation.localizationAway (Localization.Away a) a).ofAlgEquiv
    (IsLocalization.Away.mvPolynomialQuotientEquiv (Localization.Away a) a).symm).reindex
      finOneEquiv finOneEquiv

def polynomialExample : Prop := ∀ (A : Type u) [CommRing A] (n : ℕ),
  presentationStandardSmooth (polynomialPresentation A n) ∧
  (polynomialPresentation A n).dimension = n ∧
  (∀ i, (polynomialPresentation A n).val i = X i) ∧
  Algebra.IsStandardSmoothOfRelativeDimension n A (MvPolynomial (Fin n) A)

/-- The identification respects both the A-structure and the inverse variable. -/
def inverseIdentification : Prop := ∀ (A : Type u) [CommRing A] (a : A),
  ∃ e : InverseQuotient A a ≃ₐ[A] Localization.Away a,
    e (Ideal.Quotient.mk _ (X ())) = IsLocalization.Away.invSelf a

/-- The displayed variable maps to its quotient class. -/
def inverseGenerator : Prop := ∀ (A : Type u) [CommRing A] (a : A) (i : Fin 1),
  (inversePresentation A a).val i = Ideal.Quotient.mk _ (X ())

/-- The presentation retains the exact equation aT-1. -/
def inverseEquation : Prop := ∀ (A : Type u) [CommRing A] (a : A) (j : Fin 1),
  (inversePresentation A a).relation j = C a * X 0 - 1

def inverseMinor : Prop := ∀ (A : Type u) [CommRing A] (a : A),
  (selectedMinor (inversePresentation A a) (Function.Embedding.refl _)).det =
    algebraMap A (InverseQuotient A a) a

def inverseUnit : Prop := ∀ (A : Type u) [CommRing A] (a : A),
  IsUnit (algebraMap A (InverseQuotient A a) a)

def inverseExample : Prop := ∀ (A : Type u) [CommRing A] (a : A),
  presentationStandardSmooth (inversePresentation A a) ∧
  (inversePresentation A a).dimension = 0 ∧
  Algebra.IsStandardSmoothOfRelativeDimension 0 A (InverseQuotient A a)

/-- At a=0 the quotient is the zero ring, still admitted by the example. -/
def inverseZero : Prop := ∀ (A : Type u) [CommRing A],
  Subsingleton (InverseQuotient A (0 : A))

end
end Specs.AdvCommAlg.Smooth.Elementary
