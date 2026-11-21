import MathGenome.Internal.Specs.D07.Ch22.LocalizationIdeals
import MathGenome.Internal.Specs.D07.Ch09.MaximalQuotient
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.Int.Basic

/-!
Independent specifications for K07.22.local_rings, paper.tex:7169–7182.
The chapter conventions (6699–6703) permit arbitrary commutative unital
rings, including the zero ring. Primeness is the sole extra hypothesis;
it entails properness and so excludes the zero ring only when a prime
is supplied. Fractions and extended ideals are the same canonical objects
as in the upstream localization construction and ideal correspondence.
No injectivity, domain, or Noetherian assumption is added.
-/

universe u

namespace Specs.D07.Ch22.LocalRings

/-- Match the source's definition, including nonzeroness, to `IsLocalRing`. -/
def LocalCharacterization : Prop :=
  ∀ (R : Type u) [CommRing R],
    IsLocalRing R ↔ Nontrivial R ∧ ∃! M : Ideal R, M.IsMaximal

/-- R_P is nonzero, even if R has zero divisors. -/
def LocalizationNontrivial : Prop :=
  ∀ (R : Type u) [CommRing R] (P : Ideal R) [P.IsPrime],
    Nontrivial (Localization.AtPrime P)

/-- Locality refers to the canonical localization ring operations. -/
def LocalizationLocal : Prop :=
  ∀ (R : Type u) [CommRing R] (P : Ideal R) [P.IsPrime],
    IsLocalRing (Localization.AtPrime P)

/-- The numerator of a fraction is outside P exactly when the fraction is a unit. -/
def FractionUnitIff : Prop :=
  ∀ (R : Type u) [CommRing R] (P : Ideal R) [P.IsPrime]
      (a : R) (s : P.primeCompl),
    IsUnit (Localization.mk a s) ↔ a ∉ P

/-- The source's explicit inverse s/a, with both multiplication identities. -/
def FractionInverse : Prop :=
  ∀ (R : Type u) [CommRing R] (P : Ideal R) [P.IsPrime]
      (a : R) (s : P.primeCompl) (ha : a ∉ P),
    Localization.mk a s * Localization.mk (s : R) ⟨a, ha⟩ = 1 ∧
    Localization.mk (s : R) ⟨a, ha⟩ * Localization.mk a s = 1

/-- For any chosen numerator, membership in PR_P is equivalent to membership in P. -/
def FractionMemIff : Prop :=
  ∀ (R : Type u) [CommRing R] (P : Ideal R) [P.IsPrime]
      (a : R) (s : P.primeCompl),
    Localization.mk a s ∈ Ideal.map (algebraMap R (Localization.AtPrime P)) P ↔ a ∈ P

/-- All nonunits, not just images of elements of P, form the extended ideal. -/
def NonunitsExtendedIdeal : Prop :=
  ∀ (R : Type u) [CommRing R] (P : Ideal R) [P.IsPrime]
      (x : Localization.AtPrime P),
    x ∈ Ideal.map (algebraMap R (Localization.AtPrime P)) P ↔ ¬ IsUnit x

/-- Every proper ideal of R_P is contained in PR_P. -/
def ProperIdealsContained : Prop :=
  ∀ (R : Type u) [CommRing R] (P : Ideal R) [P.IsPrime]
      (J : Ideal (Localization.AtPrime P)),
    J ≠ ⊤ → J ≤ Ideal.map (algebraMap R (Localization.AtPrime P)) P

/-- The named extended ideal is maximal and is the only maximal ideal. -/
def UniqueMaximalIdeal : Prop :=
  ∀ (R : Type u) [CommRing R] (P : Ideal R) [P.IsPrime],
    (Ideal.map (algebraMap R (Localization.AtPrime P)) P).IsMaximal ∧
    ∀ J : Ideal (Localization.AtPrime P),
      J.IsMaximal → J = Ideal.map (algebraMap R (Localization.AtPrime P)) P

/-- Identify PR_P with Mathlib's nonunit maximal ideal. -/
def ExtendedIdealEqMaximal : Prop :=
  ∀ (R : Type u) [CommRing R] (P : Ideal R) [P.IsPrime],
    Ideal.map (algebraMap R (Localization.AtPrime P)) P =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)

/-- The canonical quotient operations make R_P/PR_P a field. -/
def ResidueField : Prop :=
  ∀ (R : Type u) [CommRing R] (P : Ideal R) [P.IsPrime],
    IsField (Localization.AtPrime P ⧸ Ideal.map (algebraMap R (Localization.AtPrime P)) P)

/-- Make the inverse construction explicit on representatives of nonzero classes. -/
def ResidueInverse : Prop :=
  ∀ (R : Type u) [CommRing R] (P : Ideal R) [P.IsPrime]
      (x : Localization.AtPrime P),
    Ideal.Quotient.mk (Ideal.map (algebraMap R (Localization.AtPrime P)) P) x ≠ 0 →
    ∃ y : Localization.AtPrime P,
      x * y - 1 ∈ Ideal.map (algebraMap R (Localization.AtPrime P)) P ∧
      y * x - 1 ∈ Ideal.map (algebraMap R (Localization.AtPrime P)) P

/-- Localization at a prime need not be injective: a concrete zero-divisor ring. -/
def NoninjectivityExample : Prop :=
  ∃ (P : Ideal (ℤ × ℤ)) (hP : P.IsPrime),
    letI := hP
    ¬ Function.Injective (algebraMap (ℤ × ℤ) (Localization.AtPrime P))

end Specs.D07.Ch22.LocalRings
