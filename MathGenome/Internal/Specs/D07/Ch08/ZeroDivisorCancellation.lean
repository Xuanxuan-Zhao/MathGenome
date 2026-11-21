import MathGenome.Internal.Specs.D07.Ch08.RingDefinition
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Ring.Int.Defs

/-!
Independent specifications for K07.08.zero_divisor_cancellation,
paper.tex:1247–1255. A zero divisor is required to be nonzero, and either
order of multiplication may provide its nonzero annihilator. General ring
claims allow noncommutative and trivial rings. Only the explicit failure of
zero cancellation needs nontriviality; domains are commutative and nontrivial.
-/

universe u

namespace Specs.D07.Ch08.ZeroDivisorCancellation

/-- The convention in the paper, including the nonzero requirement on `a`. -/
def IsZeroDivisor {R : Type u} [Ring R] (a : R) : Prop :=
  a ≠ 0 ∧ ∃ b : R, b ≠ 0 ∧ (a * b = 0 ∨ b * a = 0)

def ZeroDivisorCharacterization : Prop :=
  ∀ (R : Type u) [Ring R] (a : R),
    IsZeroDivisor a ↔ a ≠ 0 ∧ ∃ b : R, b ≠ 0 ∧ (a * b = 0 ∨ b * a = 0)

/-- A two-sided inverse cancels a zero product in either order. -/
def UnitZeroProducts : Prop :=
  ∀ (R : Type u) [Ring R] (a : R), IsUnit a →
    (∀ x : R, a * x = 0 → x = 0) ∧ (∀ x : R, x * a = 0 → x = 0)

def UnitNotZeroDivisor : Prop :=
  ∀ (R : Type u) [Ring R] (a : R), IsUnit a → ¬ IsZeroDivisor a

def LeftCancellation : Prop :=
  ∀ (R : Type u) [Ring R] (a : R), (∀ x : R, a * x = 0 → x = 0) →
    ∀ b c : R, a * b = a * c → b = c

def RightCancellation : Prop :=
  ∀ (R : Type u) [Ring R] (a : R), (∀ x : R, x * a = 0 → x = 0) →
    ∀ b c : R, b * a = c * a → b = c

def DomainCancellation : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (a b c : R), a ≠ 0 →
    (a * b = a * c ↔ b = c) ∧ (b * a = c * a ↔ b = c)

/-- Zero products agree for all choices of the other factor, even in a trivial ring. -/
def ZeroProducts : Prop :=
  ∀ (R : Type u) [Ring R] (b c : R),
    (0 : R) * b = 0 * c ∧ b * 0 = c * 0

/-- In every nontrivial ring these equal products can have distinct factors. -/
def ZeroCancellationFailure : Prop :=
  ∀ (R : Type u) [Ring R] [Nontrivial R],
    ∃ b c : R, b ≠ c ∧ (0 : R) * b = 0 * c ∧ b * 0 = c * 0

def IntegerTwoNeither : Prop :=
  (2 : ℤ) ≠ 0 ∧ ¬ IsUnit (2 : ℤ) ∧ ¬ IsZeroDivisor (2 : ℤ)

end Specs.D07.Ch08.ZeroDivisorCancellation
