import Mathlib.RingTheory.Localization.Defs

/-!
Independent specification for K07.22.localization_construction,
paper.tex:7044–7080 (with the chapter conventions at 6699–6703).

`Submonoid R` means precisely a subset containing one and closed under
multiplication. No nontriviality, regular-denominator, or zero-exclusion
hypothesis is imposed. We use the canonical quotient ring `Localization S`.
The relation below is the source relation, and `QuotientRepresentation`
explicitly identifies its quotient with that canonical construction.
-/

universe u

namespace Specs.D07.Ch22.LocalizationConstruction

variable {R : Type u} [CommRing R]

/-- The paper's relation, with the essential extra multiplier. -/
def FractionRel (S : Submonoid R) (p q : R × S) : Prop :=
  ∃ u : S, (u : R) * ((q.2 : R) * p.1 - (p.2 : R) * q.1) = 0

/-- Addition on representatives as given in the source. -/
def addPair {S : Submonoid R} (p q : R × S) : R × S :=
  (p.1 * (q.2 : R) + q.1 * (p.2 : R), p.2 * q.2)

/-- Multiplication on representatives as given in the source. -/
def mulPair {S : Submonoid R} (p q : R × S) : R × S :=
  (p.1 * q.1, p.2 * q.2)

/-- Negation on representatives as given in the source. -/
def negPair {S : Submonoid R} (p : R × S) : R × S := (-p.1, p.2)

/-- Exactly the stated relation characterizes equality of fractions. -/
def FractionEquality : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R) (a b : R) (s t : S),
    Localization.mk a s = Localization.mk b t ↔
      ∃ u : S, (u : R) * ((t : R) * a - (s : R) * b) = 0

/-- Reflexivity, symmetry and transitivity, with the original hypotheses. -/
def RelationEquivalence : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R), Equivalence (FractionRel S)

/-- The source's equivalence classes really are the canonical localization,
with the correspondence fixed on every representative. -/
def QuotientRepresentation : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R),
    ∃ e : Quot (FractionRel S) ≃ Localization S,
      ∀ p : R × S, e (Quot.mk (FractionRel S) p) = Localization.mk p.1 p.2

/-- Every element is represented by a numerator and a denominator in S. -/
def FractionRepresentatives : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R) (x : Localization S),
    ∃ a : R, ∃ s : S, x = Localization.mk a s

/-- The source addition formula, in the source's order of factors. -/
def AdditionFormula : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R) (a b : R) (s t : S),
    Localization.mk a s + Localization.mk b t =
      Localization.mk (a * (t : R) + b * (s : R)) (s * t)

def MultiplicationFormula : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R) (a b : R) (s t : S),
    Localization.mk a s * Localization.mk b t = Localization.mk (a * b) (s * t)

def NegationFormula : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R) (a : R) (s : S),
    -Localization.mk a s = Localization.mk (-a) s

/-- All three operations respect the original relation on representatives. -/
def OperationsWellDefined : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R) (p p' q q' : R × S),
    FractionRel S p p' → FractionRel S q q' →
      FractionRel S (addPair p q) (addPair p' q') ∧
      FractionRel S (mulPair p q) (mulPair p' q') ∧
      FractionRel S (negPair p) (negPair p')

/-- The chosen identities and the displayed additive-inverse computation. -/
def IdentityFormulas : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R),
    (Localization.mk 0 (1 : S) = 0) ∧
    (Localization.mk 1 (1 : S) = 1) ∧
    (∀ s : S, Localization.mk 0 s = 0) ∧
    (∀ (a : R) (s : S),
      Localization.mk a s + Localization.mk (-a) s = 0)

/-- Explicit laws for the canonical operations verified by the fraction formulas.
The additive group and associative, commutative, unital, distributive product
are all asserted; this is not just existence of some ring structure. -/
def RingLaws : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R),
    (∀ x y z : Localization S, (x + y) + z = x + (y + z)) ∧
    (∀ x y : Localization S, x + y = y + x) ∧
    (∀ x : Localization S, 0 + x = x) ∧
    (∀ x : Localization S, x + 0 = x) ∧
    (∀ x : Localization S, -x + x = 0) ∧
    (∀ x : Localization S, x + -x = 0) ∧
    (∀ x y z : Localization S, (x * y) * z = x * (y * z)) ∧
    (∀ x y : Localization S, x * y = y * x) ∧
    (∀ x : Localization S, 1 * x = x) ∧
    (∀ x : Localization S, x * 1 = x) ∧
    (∀ x y z : Localization S, x * (y + z) = x * y + x * z) ∧
    (∀ x y z : Localization S, (x + y) * z = x * z + y * z)

/-- Type and fixed expected value of the paper's unital map lambda. -/
def LocalizationMapType : Type (u + 1) :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R), R →+* Localization S

def LocalizationMapValue : LocalizationMapType.{u} :=
  fun R _ S => algebraMap R (Localization S)

/-- This actual unital ring homomorphism takes a to a/1. -/
def CanonicalMapFormula : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R) (a : R),
    algebraMap R (Localization S) a = Localization.mk a 1

/-- Each denominator maps to a unit; its specified two-sided inverse is 1/s. -/
def DenominatorUnits : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R) (s : S),
    IsUnit (algebraMap R (Localization S) (s : R)) ∧
    (algebraMap R (Localization S) (s : R) * Localization.mk 1 s = 1) ∧
    (Localization.mk 1 s * algebraMap R (Localization S) (s : R) = 1)

end Specs.D07.Ch22.LocalizationConstruction
