import Mathlib.RingTheory.Localization.FractionRing

/-!
Independent specifications for K07.08.fraction_field, paper.tex:1437–1479.
`FractionRing R` is Mathlib's quotient `Localization (nonZeroDivisors R)`.
For a domain these denominators are precisely the nonzero elements. The
quotient-class bridge and equality criterion below identify this quotient
with the paper's pairs modulo cross multiplication, with its stated operations.
The universal property is the separate entry K07.08.fraction_universal.
-/

universe u v

namespace Specs.D07.Ch08.FractionField

/-- The concrete quotient is a field, embeds the given ring, and consists of fractions. -/
def FieldConstruction : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R],
    IsField (FractionRing R) ∧
    Function.Injective (algebraMap R (FractionRing R)) ∧
    ∀ x : FractionRing R, ∃ a b : R, b ≠ 0 ∧
      x = algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b

/-- Existence without presupposing any fraction-field model. -/
def ExistsFractionField : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R],
    ∃ (K : Type u) (_ : Field K) (ι : R →+* K),
      Function.Injective ι ∧ ∀ x : K, ∃ a b : R, b ≠ 0 ∧ x = ι a / ι b

/-- A literal quotient class of a pair is the indicated field quotient. -/
def QuotientClass : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b : R) (hb : b ≠ 0),
    (Localization.mk a ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩ : FractionRing R) =
      algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b

def FractionEquality : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b c d : R), b ≠ 0 → d ≠ 0 →
    (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b =
      algebraMap R (FractionRing R) c / algebraMap R (FractionRing R) d ↔
      a * d = b * c)

def PairRelationEquivalence : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R],
    Equivalence (fun p q : R × {b : R // b ≠ 0} => p.1 * q.2.1 = p.2.1 * q.1)

def FractionOperations : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b c d : R), b ≠ 0 → d ≠ 0 →
    b * d ≠ 0 ∧
    (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b +
      algebraMap R (FractionRing R) c / algebraMap R (FractionRing R) d =
      algebraMap R (FractionRing R) (a * d + b * c) /
        algebraMap R (FractionRing R) (b * d)) ∧
    (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b *
      (algebraMap R (FractionRing R) c / algebraMap R (FractionRing R) d) =
      algebraMap R (FractionRing R) (a * c) /
        algebraMap R (FractionRing R) (b * d))

def ConstantsAndNegation : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R],
    (algebraMap R (FractionRing R) 0 / algebraMap R (FractionRing R) 1 = 0) ∧
    (algebraMap R (FractionRing R) 1 / algebraMap R (FractionRing R) 1 = 1) ∧
    (∀ a : R, algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) 1 =
      algebraMap R (FractionRing R) a) ∧
    ∀ a b : R, b ≠ 0 →
      -(algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b) =
        algebraMap R (FractionRing R) (-a) / algebraMap R (FractionRing R) b

def FractionZero : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b : R), b ≠ 0 →
    (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b = 0 ↔ a = 0)

def FractionInverse : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b : R), a ≠ 0 → b ≠ 0 →
    (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b)⁻¹ =
      algebraMap R (FractionRing R) b / algebraMap R (FractionRing R) a ∧
    (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b) *
      (algebraMap R (FractionRing R) b / algebraMap R (FractionRing R) a) = 1 ∧
    (algebraMap R (FractionRing R) b / algebraMap R (FractionRing R) a) *
      (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b) = 1

/-- Making a zero-product factor a unit kills its annihilator, in any ring target. -/
def AnnihilatorKilled : Prop :=
  ∀ (R : Type u) [Ring R] (S : Type v) [Ring S] (f : R →+* S) (b d : R),
    b * d = 0 → IsUnit (f b) → f d = 0

/-- The nonzero annihilator therefore prevents an injective map from inverting `b`. -/
def ZeroDivisorObstruction : Prop :=
  ∀ (R : Type u) [Ring R] (S : Type v) [Ring S] (f : R →+* S) (b d : R),
    d ≠ 0 → b * d = 0 → Function.Injective f → ¬ IsUnit (f b)

end Specs.D07.Ch08.FractionField
