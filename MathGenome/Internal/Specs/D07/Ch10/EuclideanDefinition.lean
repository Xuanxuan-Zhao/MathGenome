import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Ring.Int.Defs

/-!
Independent specification for K07.10.euclidean_definition, paper.tex:1880–1888.
The chapter's domain convention is `CommRing R` together with `IsDomain R`.
Only well-foundedness and the displayed division property are required of
the remainder relation. In particular there is no multiplicative compatibility
axiom, no uniqueness assertion, and no requirement on division by zero.

`EuclideanData` records an additional choice of quotient and remainder
functions. Its existence is equivalent to the source's existential predicate;
the predicate alone supplies neither an executable choice nor a complexity bound.
-/

universe u

namespace Specs.D07.Ch10.EuclideanDefinition

/-- The source's relation formulation, without stronger library axioms. -/
def IsEuclidean (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∃ smaller : R → R → Prop, WellFounded smaller ∧
    ∀ a b : R, b ≠ 0 → ∃ q r : R,
      a = q * b + r ∧ (r = 0 ∨ smaller r b)

/-- Chosen division data for the fixed ring operations. -/
structure EuclideanData (R : Type u) [CommRing R] [IsDomain R] where
  smaller : R → R → Prop
  wellFounded : WellFounded smaller
  quotient : R → R → R
  remainder : R → R → R
  division : ∀ a b : R, b ≠ 0 → a = quotient a b * b + remainder a b
  decrease : ∀ a b : R, b ≠ 0 → remainder a b = 0 ∨ smaller (remainder a b) b

-- Types and expected values for the two public definition aliases.
def EuclideanPredicateType : Type (u + 1) :=
  (R : Type u) → [CommRing R] → [IsDomain R] → Prop

def euclideanPredicateValue : EuclideanPredicateType.{u} := @IsEuclidean

def EuclideanDataType : Type (u + 1) :=
  (R : Type u) → [CommRing R] → [IsDomain R] → Type u

def euclideanDataValue : EuclideanDataType.{u} := @EuclideanData

def DivisionDataCharacterization : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R],
    Nonempty (EuclideanData R) ↔ IsEuclidean R

/-- Any natural-number size satisfying remainder decrease suffices;
no multiplicative property of the size is assumed. -/
def NaturalSizeSuffices : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (size : R → ℕ),
    (∀ a b : R, b ≠ 0 → ∃ q r : R,
      a = q * b + r ∧ (r = 0 ∨ size r < size b)) → IsEuclidean R

/-- Ordinary integer division, with strict decrease of absolute value.
The natural absolute value is the integer absolute value viewed in ℕ. -/
def IntegerDivisionData : Prop :=
  ∃ d : EuclideanData ℤ,
    d.smaller = (fun a b : ℤ => a.natAbs < b.natAbs) ∧
    d.quotient = (fun a b : ℤ => a / b) ∧
    d.remainder = (fun a b : ℤ => a % b)

def IntegersEuclidean : Prop := IsEuclidean ℤ

/-- In a field choose the empty relation and identically zero remainder. -/
def FieldDivisionData : Prop :=
  ∀ (K : Type u) [Field K], ∃ d : EuclideanData K,
    d.smaller = (fun _ _ : K => False) ∧
    d.quotient = (fun a b : K => a / b) ∧
    d.remainder = (fun _ _ : K => 0)

def FieldsEuclidean : Prop := ∀ (K : Type u) [Field K], IsEuclidean K

end Specs.D07.Ch10.EuclideanDefinition
