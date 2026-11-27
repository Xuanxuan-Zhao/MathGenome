import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.OperatorRing
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Ideal.Quotient.Defs

namespace GaloisFormalization.PV.Specs

universe u v w z

open scoped nonZeroDivisors

def totalQuotientRingType := (R : Type u) → [CommRing R] → Type u

abbrev totalQuotientRing : totalQuotientRingType.{u} := fun R _ => FractionRing R

/-- The quotient rule as a single fraction in the localization. -/
noncomputable def derivationFractionValue {R : Type u} {L : Type v}
    [CommRing R] [CommRing L] [Algebra R L] (M : Submonoid R) [IsLocalization M L]
    (d : Derivation ℤ R R) (r : R) (s : M) : L :=
  IsLocalization.mk' L (d r * (s : R) - r * d (s : R)) (s * s)

def localizedDerivationExistsUnique :=
  ∀ {R : Type u} {L : Type v} [CommRing R] [CommRing L] [Algebra R L]
    (M : Submonoid R) [IsLocalization M L] (d : Derivation ℤ R R),
    ∃! δ : Derivation ℤ L L, ∀ r, δ (algebraMap R L r) = algebraMap R L (d r)

def localizedDerivationQuotientRule :=
  ∀ {R : Type u} {L : Type v} [CommRing R] [CommRing L] [Algebra R L]
    (M : Submonoid R) [IsLocalization M L] (d : Derivation ℤ R R) (δ : Derivation ℤ L L),
    (∀ r, δ (algebraMap R L r) = algebraMap R L (d r)) →
    ∀ (r : R) (s : M), δ (IsLocalization.mk' L r s) = derivationFractionValue M d r s

def ringEquivNonZeroDivisors :=
  ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] (e : R ≃+* S) (s : R),
    e s ∈ S⁰ ↔ s ∈ R⁰

set_option linter.checkUnivs false in
def fractionRingEquivType :=
  {R : Type u} → {S : Type v} → {K : Type w} → {L : Type z} →
  [CommRing R] → [CommRing S] → [CommRing K] → [CommRing L] →
  [Algebra R K] → [IsFractionRing R K] → [Algebra S L] → [IsFractionRing S L] →
  (R ≃+* S) → (K ≃+* L)

noncomputable def fractionRingEquiv : fractionRingEquivType.{u, v, w, z} :=
  fun {_ _ _ _} _ _ _ _ _ _ _ _ e => IsFractionRing.ringEquivOfRingEquiv e

def fractionRingEquivOnFractions :=
  ∀ {R : Type u} {S : Type v} {K : Type w} {L : Type z}
    [CommRing R] [CommRing S] [CommRing K] [CommRing L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    (e : R ≃+* S) (r : R) (s : R⁰),
    ∃ hs : e s ∈ S⁰,
      fractionRingEquiv e (IsLocalization.mk' K r s) =
        IsLocalization.mk' L (e r) ⟨e s, hs⟩

def fractionRingEquivInverse :=
  ∀ {R : Type u} {S : Type v} {K : Type w} {L : Type z}
    [CommRing R] [CommRing S] [CommRing K] [CommRing L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    (e : R ≃+* S),
    (fractionRingEquiv (K := K) (L := L) e).symm = fractionRingEquiv e.symm

def fractionOperatorExistsUnique :=
  ∀ {kind : OperatorKind} {R : Type u} {K : Type v}
    [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K] (D : operator kind R),
    ∃! E : operator kind K, commutes D E (algebraMap R K)

def fractionOperatorEmbeddingInjective :=
  ∀ (R : Type u) (K : Type v)
    [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K],
    Function.Injective (algebraMap R K)

def fractionOperatorEquivExistsUnique :=
  ∀ {kind : OperatorKind} {R : Type u} {S : Type v} {K : Type w} {L : Type z}
    [CommRing R] [CommRing S] [CommRing K] [CommRing L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    {D : operator kind R} {E : operator kind S}
    {D' : operator kind K} {E' : operator kind L}
    (e : ringEquiv D E),
    commutes D D' (algebraMap R K) → commutes E E' (algebraMap S L) →
    ∃! e' : ringEquiv D' E', ∀ r, e'.val (algebraMap R K r) = algebraMap S L (e.val r)

def quotientOperatorExistsUnique :=
  ∀ {kind : OperatorKind} {R : Type u} [CommRing R]
    (D : operator kind R) (I : Ideal R), isStable D (I : Set R) →
    ∃! E : operator kind (R ⧸ I), commutes D E (Ideal.Quotient.mk I)

def quotientDifferenceInverse :=
  ∀ {R : Type u} [CommRing R]
    (σ : operator .difference R) (I : Ideal R) (τ : operator .difference (R ⧸ I)),
    commutes σ τ (Ideal.Quotient.mk I) →
    ∀ r, (toRingEquiv τ).symm (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk I ((toRingEquiv σ).symm r)

end GaloisFormalization.PV.Specs
