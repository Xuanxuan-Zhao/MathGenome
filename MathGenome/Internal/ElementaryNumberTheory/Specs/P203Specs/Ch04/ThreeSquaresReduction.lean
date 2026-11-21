import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Int.Basic

/-! Independent scope of the obstruction and squarefree reduction in
`paper.tex`, Theorem 4.10, lines 1874–1900. -/
namespace P203Specs.Ch04

/-- Integer coordinates, including negative coordinates and zero. -/
def ThreeSquares (n : ℕ) : Prop :=
  ∃ x y z : ℤ, (n : ℤ) = x ^ 2 + y ^ 2 + z ^ 2

/-- The excluded natural numbers, with both exponents and parameters nonnegative. -/
def Forbidden (n : ℕ) : Prop :=
  ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7)

def ThreeSquaresZero : Prop := ThreeSquares 0

def ThreeSquaresOne : Prop := ThreeSquares 1

def EvenCoordinates : Prop :=
  ∀ x y z : ℤ, (4 : ℤ) ∣ x ^ 2 + y ^ 2 + z ^ 2 →
    (2 : ℤ) ∣ x ∧ (2 : ℤ) ∣ y ∧ (2 : ℤ) ∣ z

def ModEightObstruction : Prop :=
  ∀ x y z : ℤ, (x ^ 2 + y ^ 2 + z ^ 2) % 8 ≠ 7

def FourDescent : Prop :=
  ∀ n : ℕ, ThreeSquares (4 * n) ↔ ThreeSquares n

def ForbiddenObstruction : Prop :=
  ∀ n : ℕ, Forbidden n → ¬ThreeSquares n

def SquareScaling : Prop :=
  ∀ d n : ℕ, ThreeSquares n → ThreeSquares (d ^ 2 * n)

/-- Positive square factors preserve the excluded form in both directions. -/
def ForbiddenSquareScaling : Prop :=
  ∀ d n : ℕ, 0 < d → (Forbidden (d ^ 2 * n) ↔ Forbidden n)

def SquarefreeReduction : Prop :=
  ∀ n : ℕ, 0 < n → ∃ d n₀ : ℕ,
    0 < d ∧ 0 < n₀ ∧ Squarefree n₀ ∧ n = d ^ 2 * n₀ ∧
    (Forbidden n ↔ Forbidden n₀) ∧ (ThreeSquares n₀ → ThreeSquares n)

/-- An exact characterization among squarefree naturals, including one. -/
def SquarefreeResidues : Prop :=
  ∀ n : ℕ, Squarefree n →
    (¬Forbidden n ↔ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨
      n % 8 = 5 ∨ n % 8 = 6)

end P203Specs.Ch04
