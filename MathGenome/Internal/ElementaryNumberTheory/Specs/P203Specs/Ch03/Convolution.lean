import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Data.PNat.Basic

/-! Source: paper.tex, Chapter 3 conventions and Theorem 3.1 (nt:C01).
The canonical arithmetic functions are Mathlib's `ArithmeticFunction R`.
The positive-input functions below give the source interface, with no condition
on their values. Their named ring structure is transported from the canonical
model; it is deliberately not a global instance replacing the usual Pi ring.
-/

namespace P203Specs

def PositiveFunction (R : Type*) := ℕ+ → R

/-- Zero extension is only an implementation convention at the unused input 0. -/
def zeroExtend {R : Type*} [Zero R] (f : PositiveFunction R) : ArithmeticFunction R :=
  ⟨fun n => if h : 0 < n then f ⟨n, h⟩ else 0, by simp⟩

def restrictPositive {R : Type*} [Zero R] (f : ArithmeticFunction R) :
    PositiveFunction R := fun n => f n

/-- All positive-input functions, with no extra hypothesis, are represented. -/
def positiveEquiv (R : Type*) [Zero R] : PositiveFunction R ≃ ArithmeticFunction R where
  toFun := zeroExtend
  invFun := restrictPositive
  left_inv f := by
    funext n
    dsimp [restrictPositive, zeroExtend]
    rw [dite_eq_left n.pos]
    exact congrArg f (PNat.coe_injective rfl)
  right_inv f := by
    apply ArithmeticFunction.ext
    intro n
    by_cases h : 0 < n
    · simp [restrictPositive, zeroExtend, h]
    · have hn : n = 0 := Nat.eq_zero_of_not_pos h
      simp [zeroExtend, hn]

def positiveAdd {R : Type*} [Add R] (f g : PositiveFunction R) :
    PositiveFunction R := fun n => f n + g n

/-- The displayed sum over positive divisors of n, with quotient n/d. -/
def positiveConvolution {R : Type*} [CommRing R] (f g : PositiveFunction R) :
    PositiveFunction R := fun n =>
  ∑ d : {d : ℕ // d ∈ (n : ℕ).divisors},
    f ⟨d, Nat.pos_of_mem_divisors d.property⟩ *
      g ⟨(n : ℕ) / d, Nat.div_pos
        (Nat.le_of_dvd n.pos (Nat.dvd_of_mem_divisors d.property))
        (Nat.pos_of_mem_divisors d.property)⟩

/-- The convolution identity, distinct from the constant-one function. -/
def delta (R : Type*) [Zero R] [One R] : PositiveFunction R :=
  fun n => if n = 1 then 1 else 0

/-- Transport of the standard convolution ring to the source's domain. -/
noncomputable abbrev positiveRing (R : Type*) [CommRing R] : CommRing (PositiveFunction R) :=
  (positiveEquiv R).commRing

namespace Convolution

/-- Restriction and zero extension are mutually inverse on the entire spaces. -/
def Identification : Prop :=
  ∀ (R : Type*) [CommRing R],
    (∀ f : PositiveFunction R, restrictPositive (zeroExtend f) = f) ∧
    (∀ f : ArithmeticFunction R, zeroExtend (restrictPositive f) = f) ∧
    (∀ (f : PositiveFunction R) (n : ℕ+), zeroExtend f n = f n) ∧
    (∀ f : PositiveFunction R, zeroExtend f 0 = 0)

def AdditionBridge : Prop :=
  ∀ (R : Type*) [CommRing R] (f g : PositiveFunction R),
    zeroExtend (positiveAdd f g) = zeroExtend f + zeroExtend g

def ProductBridge : Prop :=
  ∀ (R : Type*) [CommRing R] (f g : PositiveFunction R),
    zeroExtend (positiveConvolution f g) = zeroExtend f * zeroExtend g

def IdentityBridge : Prop :=
  ∀ (R : Type*) [CommRing R], zeroExtend (delta R) = (1 : ArithmeticFunction R)

/-- This CommRing structure has exactly the source's operations and identity. -/
def RingOperations : Prop :=
  ∀ (R : Type*) [CommRing R],
    letI := positiveRing R
    (∀ f g : PositiveFunction R, f + g = positiveAdd f g) ∧
    (∀ f g : PositiveFunction R, f * g = positiveConvolution f g) ∧
    (1 : PositiveFunction R) = delta R ∧
    (0 : PositiveFunction R) = (fun _ => 0) ∧
    (∀ f : PositiveFunction R, -f = (fun n => -(f n)))

def UnitCriterion : Prop :=
  ∀ (R : Type*) [CommRing R] (f : ArithmeticFunction R), IsUnit f ↔ IsUnit (f 1)

def UniqueInverse : Prop :=
  ∀ (R : Type*) [CommRing R] (f : ArithmeticFunction R), IsUnit (f 1) →
    ∃! g : ArithmeticFunction R, f * g = 1 ∧ g * f = 1

def PositiveUnitCriterion : Prop :=
  ∀ (R : Type*) [CommRing R],
    letI := positiveRing R
    ∀ f : PositiveFunction R, IsUnit f ↔ IsUnit (f 1)

/-- Existence and uniqueness expressed solely in the paper's positive-domain operations. -/
def PositiveUniqueInverse : Prop :=
  ∀ (R : Type*) [CommRing R] (f : PositiveFunction R), IsUnit (f 1) →
    ∃! g : PositiveFunction R,
      positiveConvolution f g = delta R ∧ positiveConvolution g f = delta R

end Convolution
end P203Specs
