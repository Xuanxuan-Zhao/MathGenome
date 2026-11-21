import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.QuadraticSurdRecurrence
import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.Convergents

/-! Canonical square-root states and the norm identity in paper.tex,
lines 2611–2633 and 2647–2658. The recurrence is defined without assuming
periodicity, a return point, or a Pell solution. -/
namespace P203Specs

/-- Integer states, starting at `(0,1)`, with exactness of the integer
quotient proved separately under the positive nonsquare hypothesis. -/
noncomputable def sqrtState (D : ℤ) : ℕ → ℤ × ℤ
  | 0 => (0, 1)
  | j + 1 =>
    (surdNextP (sqrtState D j).1 (sqrtState D j).2 D,
     surdNextQ (sqrtState D j).1 (sqrtState D j).2 D)

noncomputable def sqrtP (D : ℤ) (j : ℕ) : ℤ := (sqrtState D j).1
noncomputable def sqrtQ (D : ℤ) (j : ℕ) : ℤ := (sqrtState D j).2

def SqrtStateType := ℤ → ℕ → ℤ × ℤ
def SqrtParameterType := ℤ → ℕ → ℤ

/-- Initial and first integer states. -/
def SqrtStateInitial : Prop :=
  ∀ D : ℤ, sqrtP D 0 = 0 ∧ sqrtQ D 0 = 1 ∧
    sqrtP D 1 = ⌊Real.sqrt (D : ℝ)⌋ ∧
    sqrtQ D 1 = D - ⌊Real.sqrt (D : ℝ)⌋ ^ 2

/-- Every state has a nonzero integer denominator, the divisibility
invariant, and represents the actual canonical complete quotient. -/
def SqrtStateValid : Prop :=
  ∀ D : ℤ, 0 < D → ¬ IsSquare D → ∀ j : ℕ,
    sqrtQ D j ≠ 0 ∧ sqrtQ D j ∣ D - sqrtP D j ^ 2 ∧
    completeQuotient (Real.sqrt (D : ℝ)) j =
      some (((sqrtP D j : ℝ) + Real.sqrt (D : ℝ)) / (sqrtQ D j : ℝ))

/-- The digit in the recurrence is the canonical digit of `sqrt D`,
and the integer division defining the next denominator is exact. -/
def SqrtStateStep : Prop :=
  ∀ D : ℤ, 0 < D → ¬ IsSquare D → ∀ j : ℕ, ∃ a : ℤ,
    partialQuotient (Real.sqrt (D : ℝ)) j = some a ∧
    sqrtP D (j + 1) = a * sqrtQ D j - sqrtP D j ∧
    sqrtQ D (j + 1) = (D - sqrtP D (j + 1) ^ 2) / sqrtQ D j ∧
    sqrtQ D j * sqrtQ D (j + 1) = D - sqrtP D (j + 1) ^ 2

/-- Exact integer norm at every index, including zero, using the source's
signed-index convergent sequences and the same canonical states. -/
def SqrtConvergentNorm : Prop :=
  ∀ D : ℤ, 0 < D → ¬ IsSquare D → ∀ n : ℕ,
    convergentNumerator (Real.sqrt (D : ℝ)) n ^ 2 -
      D * convergentDenominator (Real.sqrt (D : ℝ)) n ^ 2 =
      (-1 : ℤ) ^ (n + 1) * sqrtQ D (n + 1)

/-- Both denominators arising when solving the tail identity and rationalizing
are nonzero. No return condition is needed. -/
def SqrtConvergentDenominators : Prop :=
  ∀ D : ℤ, 0 < D → ¬ IsSquare D → ∀ n : ℕ,
    (convergentDenominator (Real.sqrt (D : ℝ)) n : ℝ) * Real.sqrt (D : ℝ) -
      (convergentNumerator (Real.sqrt (D : ℝ)) n : ℝ) ≠ 0 ∧
    D * convergentDenominator (Real.sqrt (D : ℝ)) n ^ 2 -
      convergentNumerator (Real.sqrt (D : ℝ)) n ^ 2 ≠ 0

end P203Specs
