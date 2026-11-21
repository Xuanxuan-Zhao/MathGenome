import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Units.Defs

/-!
Independent specifications for K07.10.divisibility (paper.tex:1810–1817).
The chapter's domain convention is expressed by `CommRing R` and `IsDomain R`:
in particular the domain is nontrivial. Divisibility is the canonical relation
on these ring operations, including zero. Its existential convention is
`b = a * c`, exactly as in the source. The two final propositions compare
divisibility in the specified ambient rings, ℚ and ℤ.
-/

universe u

namespace Specs.D07.Ch10.Divisibility

def DivisibilityCharacterization : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b : R),
    a ∣ b ↔ ∃ c : R, b = a * c

def DividesZero : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a : R), a ∣ 0

def ZeroDividesIff : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (b : R),
    (0 : R) ∣ b ↔ b = 0

def DivisibilityReflexive : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a : R), a ∣ a

def DivisibilityTransitive : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b d : R),
    a ∣ b → b ∣ d → a ∣ d

def UnitDivides : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b : R),
    IsUnit a → a ∣ b

def DividesOneIffIsUnit : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a : R),
    a ∣ 1 ↔ IsUnit a

def RationalTwoDividesOne : Prop := (2 : ℚ) ∣ 1

def IntegerTwoNotDividesOne : Prop := ¬ (2 : ℤ) ∣ 1

end Specs.D07.Ch10.Divisibility
