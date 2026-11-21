import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Set.Finite.Basic

/-! Independent statements for the sharpness clause of paper.tex, §5.7.
Denominators are positive integers and reduced means nonnegative gcd equal to one. -/
noncomputable section
namespace P203Specs.Ch05.HurwitzOptimality

def golden : ℝ := (1 + Real.sqrt 5) / 2

def conjugate : ℝ := (1 - Real.sqrt 5) / 2

def approximations (C : ℝ) : Set (ℤ × ℤ) :=
  {a | 0 < a.2 ∧ Int.gcd a.1 a.2 = 1 ∧
    |golden - (a.1 : ℝ) / (a.2 : ℝ)| < 1 / (C * (a.2 : ℝ) ^ 2)}

def GoldenIrrational : Prop := Irrational golden ∧ Irrational conjugate

def IntegerObstruction : Prop :=
  ∀ p q : ℤ, 0 < q →
    p ^ 2 - p * q - q ^ 2 ≠ 0 ∧
    1 ≤ |((p ^ 2 - p * q - q ^ 2 : ℤ) : ℝ)| ∧
    |((p ^ 2 - p * q - q ^ 2 : ℤ) : ℝ)| =
      (q : ℝ) ^ 2 * |(p : ℝ) / q - golden| * |(p : ℝ) / q - conjugate|

def FiniteApproximations : Prop :=
  ∀ C : ℝ, Real.sqrt 5 < C → (approximations C).Finite

def NotInfiniteApproximations : Prop :=
  ∀ C : ℝ, Real.sqrt 5 < C → ¬ (approximations C).Infinite

end P203Specs.Ch05.HurwitzOptimality
