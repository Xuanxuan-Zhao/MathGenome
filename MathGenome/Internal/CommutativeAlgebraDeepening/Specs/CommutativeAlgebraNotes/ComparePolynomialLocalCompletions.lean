import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Polynomial.Quotient

namespace CommutativeAlgebraNotes.PolynomialLocalCompletion

open IsLocalRing

/-- The completion of a local ring at its maximal ideal. -/
abbrev Completion (R : Type*) [CommRing R] [IsLocalRing R] :=
  AdicCompletion (maximalIdeal R) R

/-- The coefficientwise extension of the completion map to polynomials. -/
noncomputable abbrev coefficientMap (R : Type*) [CommRing R] [IsLocalRing R] :
    Polynomial R →+* Polynomial (Completion R) :=
  Polynomial.mapRingHom (algebraMap R (Completion R))

/-- The extension of the given polynomial ideal to the completed coefficient ring. -/
noncomputable abbrev extendedIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    (P : Ideal (Polynomial R)) : Ideal (Polynomial (Completion R)) :=
  P.map (coefficientMap R)

namespace Specs

def primeComparison : Prop :=
  ∀ (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (P : Ideal (Polynomial R)) [P.IsPrime],
    maximalIdeal R ≤ P.comap Polynomial.C →
      (extendedIdeal P).IsPrime ∧ (extendedIdeal P).comap (coefficientMap R) = P

def quotientComparison : Prop :=
  ∀ (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (P : Ideal (Polynomial R)) [P.IsPrime],
    maximalIdeal R ≤ P.comap Polynomial.C →
      ∀ n : ℕ, ∃ e : (Polynomial R ⧸ P ^ n) ≃+*
          (Polynomial (Completion R) ⧸ extendedIdeal P ^ n),
        ∀ p : Polynomial R, e (Ideal.Quotient.mk (P ^ n) p) =
          Ideal.Quotient.mk (extendedIdeal P ^ n) (coefficientMap R p)

def completionComparison : Prop :=
  ∀ (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (P : Ideal (Polynomial R)) [P.IsPrime],
    maximalIdeal R ≤ P.comap Polynomial.C →
      ∃ hPrime : (extendedIdeal P).IsPrime,
      ∃ hComap : P = (extendedIdeal P).comap (coefficientMap R),
        letI := hPrime
        ∃ e : Completion (Localization.AtPrime P) ≃+*
            Completion (Localization.AtPrime (extendedIdeal P)),
          ∀ x : Localization.AtPrime P,
            e (algebraMap (Localization.AtPrime P) _ x) =
              algebraMap (Localization.AtPrime (extendedIdeal P)) _
                (Localization.localRingHom P (extendedIdeal P) (coefficientMap R) hComap x)

end Specs
end CommutativeAlgebraNotes.PolynomialLocalCompletion
