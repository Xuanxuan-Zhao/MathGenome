import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Definitions
import Mathlib.RingTheory.Localization.Away.Basic

/-! ET-08 (paper.tex, Proposition 4.8). Arbitrary commutative unital rings,
including the zero ring; there is no finiteness hypothesis on the formal claim.
The principal ideal `Ideal.span {e}` is the ideal Ae. -/
namespace Specs.AdvCommAlg.Etale.Quotients

universe u

def formallyEtaleQuotient : Prop := ∀ (A : Type u) [CommRing A] (I : Ideal A),
  FormalLifting.formallyEtaleValue A (A ⧸ I) ↔ I ^ 2 = I

def finitePresentationQuotient : Prop := ∀ (A : Type u) [CommRing A] (I : Ideal A),
  Algebra.FinitePresentation A (A ⧸ I) ↔ I.FG

def etaleQuotient : Prop := ∀ (A : Type u) [CommRing A] (I : Ideal A),
  etaleValue A (A ⧸ I) ↔ ∃ e : A, e * e = e ∧ I = Ideal.span {e}

/-- The canonical A-algebra isomorphism, for every displayed idempotent generator. -/
def quotientLocalizationType := ∀ (A : Type u) [CommRing A] (I : Ideal A)
  (e : A), e * e = e → I = Ideal.span {e} →
  (A ⧸ I) ≃ₐ[A] Localization.Away (1 - e)

noncomputable def quotientLocalizationValue : quotientLocalizationType.{u} := by
  intro A _ I e he hI
  have hid : IsIdempotentElem e := he
  letI : IsLocalization.Away (1 - e) (A ⧸ I) :=
    IsLocalization.away_of_isIdempotentElem hid.one_sub
      (by simpa only [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, sub_sub_cancel]
          using hI) Ideal.Quotient.mk_surjective
  exact IsLocalization.algEquiv (Submonoid.powers (1 - e)) (A ⧸ I)
    (Localization.Away (1 - e))

/-- This specifies the isomorphism on every residue class, hence uniquely. -/
def quotientLocalizationApply : Prop := ∀ (A : Type u) [CommRing A]
  (I : Ideal A) (e : A) (he : e * e = e) (hI : I = Ideal.span {e}) (a : A),
  quotientLocalizationValue A I e he hI (Ideal.Quotient.mk I a) =
    algebraMap A (Localization.Away (1 - e)) a

end Specs.AdvCommAlg.Etale.Quotients
