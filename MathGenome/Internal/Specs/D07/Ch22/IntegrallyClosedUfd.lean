import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.RingTheory.Algebraic.Defs

/-!
Independent statements for K07.22.integrally_closed_ufd,
paper.tex:7269–7285 (chapters/M07.22.tex:573).

The domain and UFD hypotheses are separate: `IsIntegrallyClosed` alone
does not assert nontriviality. Membership in the coefficient ring is
expressed by the image of its unital algebra map. The general fraction
field statements include the concrete `FractionRing R` model.

Reducedness means exactly that no prime divides both entries, rather
than Bezout coprimality (which would be stronger in a general UFD).
The numerator may be zero. The final example keeps the coefficient
rings ℤ and ℚ distinct.
-/

universe u v

namespace Specs.D07.Ch22.IntegrallyClosedUfd

def IntegrallyClosedCharacterization : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R],
    IsIntegrallyClosed R ↔
      ∀ x : FractionRing R, IsIntegral R x →
        ∃ a : R, algebraMap R (FractionRing R) a = x

def UfdIsIntegrallyClosed : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R],
    IsIntegrallyClosed R

def IntegralFractionInRing : Prop :=
  ∀ (R : Type u) (K : Type v) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [Field K] [Algebra R K] [IsFractionRing R K],
    ∀ x : K, IsIntegral R x → ∃ a : R, algebraMap R K a = x

def ReducedRepresentation : Prop :=
  ∀ (R : Type u) (K : Type v) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [Field K] [Algebra R K] [IsFractionRing R K],
    ∀ x : K, ∃ r s : R, s ≠ 0 ∧
      x = algebraMap R K r / algebraMap R K s ∧
      ∀ p : R, Prime p → p ∣ r → p ∣ s → False

/-- The unit conclusion holds for every reduced presentation, including 0/s. -/
def ReducedIntegralDenominator : Prop :=
  ∀ (R : Type u) (K : Type v) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [Field K] [Algebra R K] [IsFractionRing R K]
    (r s : R), s ≠ 0 →
      (∀ p : R, Prime p → p ∣ r → p ∣ s → False) →
      IsIntegral R (algebraMap R K r / algebraMap R K s) → IsUnit s

def ZeroBoundary : Prop :=
  ∀ (R : Type u) (K : Type v) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K],
    (algebraMap R K 0 / algebraMap R K 1 = 0) ∧
    IsIntegral R (0 : K) ∧
    (∀ p : R, Prime p → p ∣ (0 : R) → p ∣ (1 : R) → False)

def RationalHalfExample : Prop :=
  ¬ IsIntegral ℤ (1 / 2 : ℚ) ∧ IsAlgebraic ℚ (1 / 2 : ℚ)

end Specs.D07.Ch22.IntegrallyClosedUfd
