import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch06.PellConvergentNorm
import Mathlib.Dynamics.PeriodicPts.Defs

/-! The periodic shape and exact return points of paper.tex,
Lemma `lem:nt-pell-return` (2593–2610, 2617–2645).
All states and digits are the upstream canonical, zero-based objects. -/
namespace P203Specs

/-- The least orbit period of the first complete quotient of `sqrt D`.
Positivity, and identification with the least digit period, are theorems below. -/
noncomputable def sqrtPeriod (D : ℤ) : ℕ :=
  Function.minimalPeriod continuedFractionStep (continuedFractionStep (Real.sqrt (D : ℝ)))

def SqrtPeriodType := ℤ → ℕ

/-- Every later canonical state is reduced and has positive integer denominator.
The representation and integrality use precisely `sqrtP` and `sqrtQ`, rather
than existentially chosen surd parameters. -/
def SqrtReducedStates : Prop :=
  ∀ D : ℤ, 0 < D → ¬ IsSquare D → ∀ j : ℕ, 1 ≤ j →
    0 < sqrtQ D j ∧
    ReducedQuadratic (((sqrtP D j : ℝ) + Real.sqrt (D : ℝ)) / (sqrtQ D j : ℝ)) ∧
    completeQuotient (Real.sqrt (D : ℝ)) j =
      some (((sqrtP D j : ℝ) + Real.sqrt (D : ℝ)) / (sqrtQ D j : ℝ))

/-- The first complete quotient has the same least positive period in its
canonical digits and in its quotient orbit. The original square root has
head `a₀`, followed by a repeating block of length `sqrtPeriod D`. Its last
entry is `2*a₀`, as specified separately below. No middle entries are required
when the period equals one. -/
def SqrtPeriodicity : Prop :=
  ∀ D : ℤ, 0 < D → ¬ IsSquare D →
    let s := Real.sqrt (D : ℝ)
    let z := continuedFractionStep s
    0 < sqrtPeriod D ∧
    completeQuotient s 1 = some z ∧
    PurelyPeriodicCF z ∧
    (∀ n : ℕ, partialQuotient z (n + sqrtPeriod D) = partialQuotient z n) ∧
    (∀ r : ℕ, 0 < r →
      (∀ n : ℕ, partialQuotient z (n + r) = partialQuotient z n) → sqrtPeriod D ≤ r) ∧
    (∀ n : ℕ, partialQuotient s (n + 1 + sqrtPeriod D) = partialQuotient s (n + 1)) ∧
    (∀ r : ℕ, 0 < r →
      (∀ n : ℕ, partialQuotient s (n + 1 + r) = partialQuotient s (n + 1)) →
      sqrtPeriod D ≤ r) ∧
    continuedFractionStep^[sqrtPeriod D] z = z ∧
    (∀ r : ℕ, 0 < r → continuedFractionStep^[r] z = z → sqrtPeriod D ≤ r)

/-- The final complete quotient and digit of the least block. -/
def SqrtPeriodLast : Prop :=
  ∀ D : ℤ, 0 < D → ¬ IsSquare D →
    completeQuotient (Real.sqrt (D : ℝ)) (sqrtPeriod D) =
      some (Real.sqrt (D : ℝ) + (⌊Real.sqrt (D : ℝ)⌋ : ℝ)) ∧
    partialQuotient (Real.sqrt (D : ℝ)) (sqrtPeriod D) =
      some (2 * ⌊Real.sqrt (D : ℝ)⌋)

/-- Exact returns, with the initial `Q₀=1` recorded separately. -/
def SqrtReturnPoints : Prop :=
  ∀ D : ℤ, 0 < D → ¬ IsSquare D →
    sqrtQ D 0 = 1 ∧ ∀ j : ℕ, 1 ≤ j →
      (sqrtQ D j = 1 ↔ sqrtPeriod D ∣ j)

end P203Specs
