import Mathlib.RingTheory.Localization.Defs

/-!
Independent statements for Theorem 4.1 (paper.tex, ring of fractions).
The ring is Mathlib's quotient `Localization S`; its unital map is
`algebraMap R (Localization S)` and `Localization.mk a s` denotes a/s.
No nontriviality or regularity assumption is imposed on R or S.
-/

namespace P103.Ch04.RingLocalizationSpecs

universe u v

variable (R : Type u) [CommRing R] (S : Submonoid R)

def DenominatorsAreUnits : Prop :=
  ∀ s : S, IsUnit (algebraMap R (Localization S) (s : R))

def EveryElementIsFraction : Prop :=
  ∀ x : Localization S, ∃ (a : R) (s : S), x = Localization.mk a s

def FractionOverOne : Prop :=
  ∀ a : R, Localization.mk a (1 : S) = algebraMap R (Localization S) a

def FractionAddition : Prop :=
  ∀ (a b : R) (s t : S),
    Localization.mk a s + Localization.mk b t =
      Localization.mk ((t : R) * a + (s : R) * b) (s * t)

def FractionMultiplication : Prop :=
  ∀ (a b : R) (s t : S),
    Localization.mk a s * Localization.mk b t = Localization.mk (a * b) (s * t)

def FractionEquality : Prop :=
  ∀ (a b : R) (s t : S),
    Localization.mk a s = Localization.mk b t ↔
      ∃ u : S, (u : R) * ((t : R) * a - (s : R) * b) = 0

/-- A subsingleton unital ring is precisely a zero ring. -/
def ZeroRingCriterion : Prop :=
  Subsingleton (Localization S) ↔ (0 : R) ∈ S

def UniversalProperty : Prop :=
  ∀ (B : Type v) [CommRing B] (g : R →+* B),
    (∀ s : S, IsUnit (g (s : R))) →
      ∃! f : Localization S →+* B, f.comp (algebraMap R (Localization S)) = g

/-- `Ring.inverse` is the inverse of a unit in a ring, with no field assumption. -/
def FactorizationValue : Prop :=
  ∀ (B : Type v) [CommRing B] (g : R →+* B),
    (∀ s : S, IsUnit (g (s : R))) →
      ∀ f : Localization S →+* B,
        f.comp (algebraMap R (Localization S)) = g →
          ∀ (a : R) (s : S),
            f (Localization.mk a s) = g a * Ring.inverse (g (s : R))

/- Full proposition types, including all parameters, for independent bindings. -/
def DenominatorsAreUnitsType : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R), DenominatorsAreUnits R S

def EveryElementIsFractionType : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R), EveryElementIsFraction R S

def FractionOverOneType : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R), FractionOverOne R S

def FractionAdditionType : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R), FractionAddition R S

def FractionMultiplicationType : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R), FractionMultiplication R S

def FractionEqualityType : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R), FractionEquality R S

def ZeroRingCriterionType : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R), ZeroRingCriterion R S

def UniversalPropertyType : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R), UniversalProperty.{u, v} R S

def FactorizationValueType : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R), FactorizationValue.{u, v} R S

end P103.Ch04.RingLocalizationSpecs
