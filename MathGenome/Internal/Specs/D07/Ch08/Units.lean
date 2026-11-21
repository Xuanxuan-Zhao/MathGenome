import MathGenome.Internal.Specs.D07.Ch08.RingDefinition
import MathGenome.Internal.Specs.D07.Ch08.UnitsOneSidedInverseCounterexample
import Mathlib.Algebra.Field.Rat

/-!
Independent specification for K07.08.units, paper.tex:1210–1228.
The rings may be noncommutative or trivial. `IsUnit` describes an element
of the ambient ring; `Rˣ` bundles such an element with its two-sided inverse.
The group assertion retains the usual multiplication, identity and inverse
on these bundled units, and the value laws identify their ring operations.
The infinite-dimensional example uses the upstream canonical free space
and its standard basis and shifts, rather than a finite-dimensional space.
-/

universe u

namespace Specs.D07.Ch08.Units

def UnitCharacterization : Prop :=
  ∀ (R : Type u) [Ring R] (a : R),
    IsUnit a ↔ ∃ b : R, a * b = 1 ∧ b * a = 1

def InverseUnique : Prop :=
  ∀ (R : Type u) [Ring R] (a b c : R),
    a * b = 1 → b * a = 1 → a * c = 1 → c * a = 1 → b = c

/-- The group must use the canonical monoid and inverse on `Rˣ`. -/
def UnitsFormGroup : Prop :=
  ∀ (R : Type u) [Ring R],
    ∃ g : Group Rˣ,
      g.toMonoid = (inferInstance : Monoid Rˣ) ∧
      g.toInv = (inferInstance : Inv Rˣ)

/-- Multiplication and identity are inherited from the ring; the bundled
inverse is a two-sided ring inverse. In particular this records closure. -/
def UnitsValueLaws : Prop :=
  ∀ (R : Type u) [Ring R] (a b : Rˣ),
    ((a * b : Rˣ) : R) = (a : R) * (b : R) ∧
    ((1 : Rˣ) : R) = 1 ∧
    (a : R) * ((a⁻¹ : Rˣ) : R) = 1 ∧
    ((a⁻¹ : Rˣ) : R) * (a : R) = 1

def InverseProduct : Prop :=
  ∀ (R : Type u) [Ring R] (a b : Rˣ), (a * b)⁻¹ = b⁻¹ * a⁻¹

def LeftRightInverseUnique : Prop :=
  ∀ (R : Type u) [Ring R] (a s t : R), s * a = 1 → a * t = 1 → s = t

open UnitsOneSidedInverseCounterexample in
def ShiftCounterexample : Prop :=
  ∀ (K : Type u) [Field K],
    (∀ i : ℕ, standardBasis K i = e K i) ∧
    (∀ i : ℕ, T K (e K i) = e K (i + 1)) ∧
    S K (e K 0) = 0 ∧
    (∀ i : ℕ, S K (e K (i + 1)) = e K i) ∧
    S K * T K = 1 ∧
    (T K * S K) (e K 0) = 0 ∧ e K 0 ≠ 0 ∧
    T K * S K ≠ 1 ∧ ¬ IsUnit (T K) ∧ ¬ IsUnit (S K)

def RationalTwoIsUnit : Prop := IsUnit (2 : ℚ)

def IntegerUnits : Prop := ∀ a : ℤ, IsUnit a ↔ a = 1 ∨ a = -1

def IntegerTwoNotIsUnit : Prop := ¬ IsUnit (2 : ℤ)

end Specs.D07.Ch08.Units
