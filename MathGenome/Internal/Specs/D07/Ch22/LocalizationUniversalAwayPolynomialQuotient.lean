import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-!
Independent specification for the presentation in K07.22.localization_universal,
paper.tex:7115–7124, with the commutative unital conventions at 6699–6703.
No nontriviality, domain, or nonnilpotence hypothesis is imposed.
`AdjoinRoot (C f * X - 1)` unfolds to the literal principal-ideal quotient below.
-/

universe u v

namespace Specs.D07.Ch22.LocalizationUniversalAwayPolynomialQuotient

open Polynomial

/-- The literal quotient R[T]/(C(f)T - 1). -/
abbrev Presentation (R : Type u) [CommRing R] (f : R) :=
  Polynomial R ⧸ Ideal.span ({C f * X - 1} : Set (Polynomial R))

/-- The quotient projection, including on constants and on the variable. -/
noncomputable def quotientMap {R : Type u} [CommRing R] (f : R) :
    Polynomial R →+* Presentation R f := Ideal.Quotient.mk _

/-- An actual equivalence of R-algebras, for every ring and every f. -/
def EquivalenceType : Type (u + 1) :=
  ∀ (R : Type u) [CommRing R] (f : R),
    Localization.Away f ≃ₐ[R] Presentation R f

/-- Fix the canonical equivalence, constructed by the two universal lifts. -/
noncomputable def equivalenceValue : EquivalenceType.{u} :=
  fun _ _ f => Localization.awayEquivAdjoin f

/-- Evaluation T ↦ 1/f factors through precisely the displayed quotient. -/
def EvaluationFormula : Prop :=
  ∀ (R : Type u) [CommRing R] (f : R) (p : Polynomial R),
    (equivalenceValue R f).symm (quotientMap f p) =
      aeval (IsLocalization.Away.invSelf f : Localization.Away f) p

/-- In the other direction 1/f is sent to the class of T. -/
def InverseGenerator : Prop :=
  ∀ (R : Type u) [CommRing R] (f : R),
    equivalenceValue R f (IsLocalization.Away.invSelf f) = quotientMap f X

/-- Both directions fix the coefficient ring. -/
def CoefficientFormulas : Prop :=
  ∀ (R : Type u) [CommRing R] (f a : R),
    equivalenceValue R f (algebraMap R (Localization.Away f) a) = quotientMap f (C a) ∧
    (equivalenceValue R f).symm (quotientMap f (C a)) =
      algebraMap R (Localization.Away f) a

/-- The relation makes the class of T an inverse of the class of f. -/
def QuotientInverse : Prop :=
  ∀ (R : Type u) [CommRing R] (f : R),
    algebraMap R (Presentation R f) f * quotientMap f X = 1 ∧
    quotientMap f X * algebraMap R (Presentation R f) f = 1

/-- The evaluation lift is the unique R-algebra map with the stated generator.
The forward map is the unique R-algebra extension from the localization. -/
def UniversalMaps : Prop :=
  ∀ (R : Type u) [CommRing R] (f : R),
    (∀ h : Presentation R f →ₐ[R] Localization.Away f,
      h (quotientMap f X) = IsLocalization.Away.invSelf f →
      h = (equivalenceValue R f).symm.toAlgHom) ∧
    (∀ h : Localization.Away f →ₐ[R] Presentation R f,
      h = (equivalenceValue R f).toAlgHom)

/-- Both composites of the universal lifts are the identity homomorphisms. -/
def InverseComposites : Prop :=
  ∀ (R : Type u) [CommRing R] (f : R),
    (equivalenceValue R f).symm.toAlgHom.comp (equivalenceValue R f).toAlgHom =
        AlgHom.id R (Localization.Away f) ∧
    (equivalenceValue R f).toAlgHom.comp (equivalenceValue R f).symm.toAlgHom =
        AlgHom.id R (Presentation R f)

/-- Nilpotent f makes both rings zero; zero rings are represented by Subsingleton. -/
def NilpotentCase : Prop :=
  ∀ (R : Type u) [CommRing R] (f : R), IsNilpotent f →
    Subsingleton (Localization.Away f) ∧ Subsingleton (Presentation R f)

/-- Explicit applicability to the zero coefficient ring. -/
def ZeroRingCase : Prop :=
  ∀ (R : Type u) [CommRing R] [Subsingleton R] (f : R),
    Subsingleton (Localization.Away f) ∧ Subsingleton (Presentation R f)

end Specs.D07.Ch22.LocalizationUniversalAwayPolynomialQuotient
