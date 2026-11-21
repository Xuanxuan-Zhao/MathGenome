import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Prime.Defs

/-!
Independent specifications for K07.10.irreducible_nonprime
(paper.tex:1863–1879). The canonical quadratic ring has integer coordinates
and relation `sqrtd * sqrtd = -5`. Its faithful complex realization below
identifies it with the displayed ring of numbers `a + b √(-5)`.
The norm is the library's integer-valued quadratic norm, not the complex
absolute value. All assertions here are full proposition types.
-/

namespace Specs.D07.Ch10.IrreducibleNonprime

abbrev R := Zsqrtd (-5)

/-- The positive-imaginary complex square root of `-5`. -/
noncomputable def root : ℂ := ⟨0, Real.sqrt 5⟩

/-- The coordinate realization of the quadratic ring in `ℂ`. -/
noncomputable def toComplex (z : R) : ℂ :=
  (z.re : ℂ) + (z.im : ℂ) * root

def ComplexRealization : Prop :=
  root * root = (-5 : ℂ) ∧
  Function.Injective toComplex ∧
  toComplex 1 = 1 ∧
  (∀ z w : R, toComplex (z + w) = toComplex z + toComplex w ∧
    toComplex (z * w) = toComplex z * toComplex w) ∧
  (∀ z : R, toComplex (star z) = star (toComplex z)) ∧
  Set.range toComplex = {w : ℂ | ∃ a b : ℤ, w = (a : ℂ) + (b : ℂ) * root}

def Domain : Prop := IsDomain R

def NormFormula : Prop :=
  ∀ a b : ℤ, Zsqrtd.norm (⟨a, b⟩ : R) = a ^ 2 + 5 * b ^ 2

def NormMultiplicative : Prop :=
  ∀ z w : R, Zsqrtd.norm (z * w) = Zsqrtd.norm z * Zsqrtd.norm w

def ConjugateNorm : Prop :=
  ∀ z : R, z * star z = (Zsqrtd.norm z : R) ∧
    star z * z = (Zsqrtd.norm z : R)

def NormNonnegativeAndZero : Prop :=
  (∀ z : R, 0 ≤ Zsqrtd.norm z) ∧
  (∀ z : R, Zsqrtd.norm z = 0 ↔ z = 0)

def NormOne : Prop :=
  ∀ z : R, Zsqrtd.norm z = 1 ↔ z = 1 ∨ z = -1

def Units : Prop :=
  ∀ z : R, IsUnit z ↔ z = 1 ∨ z = -1

def ConjugateInverse : Prop :=
  ∀ z : R, IsUnit z → z * star z = 1 ∧ star z * z = 1

def NormThreeImpossible : Prop :=
  ∀ a b : ℤ, a ^ 2 + 5 * b ^ 2 ≠ 3

def ThreeIrreducible : Prop := Irreducible (3 : R)

/-- Divisibility by an integer is exactly coordinatewise integer divisibility. -/
def IntegerDivisibility : Prop :=
  ∀ (n : ℤ) (z : R), (n : R) ∣ z ↔ n ∣ z.re ∧ n ∣ z.im

def WitnessProduct : Prop :=
  ((2 : R) + Zsqrtd.sqrtd) * ((2 : R) - Zsqrtd.sqrtd) = 9

def ThreeDividesProduct : Prop :=
  (3 : R) ∣ ((2 : R) + Zsqrtd.sqrtd) * ((2 : R) - Zsqrtd.sqrtd)

def ThreeNotDividesFactors : Prop :=
  ¬(3 : R) ∣ ((2 : R) + Zsqrtd.sqrtd) ∧
  ¬(3 : R) ∣ ((2 : R) - Zsqrtd.sqrtd)

def ThreeNotPrime : Prop := ¬Prime (3 : R)

end Specs.D07.Ch10.IrreducibleNonprime
