import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-! The complex subring in paper.tex:2068–2077, with its original embedding.
The chosen square root of -19 has positive imaginary part. The integer norm
is defined independently as the floor of complex norm squared; the theorems
assert that no rounding occurs on this subring. -/
noncomputable section
namespace D07.Ch10.PidNotEuclideanQuadraticIntegerNorm

def sqrtMinus19 : ℂ := ⟨0, Real.sqrt 19⟩
def omega : ℂ := (1 + sqrtMinus19) / 2
/-- The smallest unital subring of ℂ containing omega, namely ℤ[omega]. -/
def integerRing : Subring ℂ := Subring.closure {omega}
abbrev R := ↥integerRing

def expression (a b : ℤ) : ℂ := (a : ℂ) + (b : ℂ) * omega

def norm (z : R) : ℤ := ⌊Complex.normSq (z : ℂ)⌋

namespace Specs

def SquareRootPresentation : Prop :=
  sqrtMinus19 ^ 2 = (-19 : ℂ) ∧ 0 < sqrtMinus19.im ∧
    omega = (1 + sqrtMinus19) / 2

def QuadraticRelation : Prop := omega ^ 2 - omega + 5 = 0

def CoordinateMembership : Prop :=
  ∀ z : ℂ, z ∈ integerRing ↔ ∃ a b : ℤ, z = expression a b

def UniqueCoordinates : Prop :=
  ∀ z : R, ∃! p : ℤ × ℤ, (z : ℂ) = expression p.1 p.2

def NormFormula : Prop :=
  ∀ (z : R) (a b : ℤ), (z : ℂ) = expression a b →
    norm z = a ^ 2 + a * b + 5 * b ^ 2

def NormConjugate : Prop :=
  ∀ z : R, (norm z : ℂ) = (z : ℂ) * star (z : ℂ)

def CompletedSquare : Prop :=
  ∀ a b : ℤ, Complex.normSq (expression a b) =
    ((a : ℝ) + (b : ℝ) / 2) ^ 2 + 19 * (b : ℝ) ^ 2 / 4

def MultiplicativeNorm : Prop :=
  norm 0 = 0 ∧ norm 1 = 1 ∧ ∀ z w : R, norm (z * w) = norm z * norm w

def PositiveNorm : Prop :=
  (∀ z : R, 0 ≤ norm z) ∧ (∀ z : R, norm z = 0 ↔ z = 0) ∧
    ∀ z : R, z ≠ 0 → 0 < norm z

def NonzeroSecondCoordinateBound : Prop :=
  ∀ (z : R) (a b : ℤ), (z : ℂ) = expression a b → b ≠ 0 → 5 ≤ norm z

def NormOne : Prop := ∀ z : R, norm z = 1 ↔ z = 1 ∨ z = -1

def Units : Prop := ∀ z : R, IsUnit z ↔ z = 1 ∨ z = -1

end Specs
end D07.Ch10.PidNotEuclideanQuadraticIntegerNorm
