import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch06.FundamentalPellSolution
import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch06.PellSigns

/-! Independent statements of paper.tex, cor:nt-pell-minus (2739–2763).
All coefficients are integers in the same order Z[sqrt D], for every positive
nonsquare D, with the canonical least period from Chapter 5. -/
namespace P203Specs.Ch06.NegativePellSolutions
open P203Specs.Ch06.PellUnits
open P203Specs.Ch06.FundamentalPellSolution

/-- The least integral norm-minus-one unit greater than one in real order. -/
def LeastNegative (D : ℤ) (u : IntegralQuadratic D) : Prop :=
  norm u = -1 ∧ 1 < realValue D u ∧
    ∀ v : IntegralQuadratic D, norm v = -1 → 1 < realValue D v →
      realValue D u ≤ realValue D v

def EvenNonexistence : Prop :=
  ∀ D : ℤ, 0 < D → ¬IsSquare D → Even (P203Specs.sqrtPeriod D) →
    ¬ ∃ x y : ℤ, 0 < x ∧ 0 < y ∧ x ^ 2 - D * y ^ 2 = -1

def NegativeExists : Prop :=
  ∀ D : ℤ, 0 < D → ¬IsSquare D → Odd (P203Specs.sqrtPeriod D) →
    ∃! u : IntegralQuadratic D, LeastNegative D u

def NegativeCoordinates : Prop :=
  ∀ D : ℤ, 0 < D → ∀ u : IntegralQuadratic D, LeastNegative D u →
    IsUnit u ∧ 0 < u.re ∧ 0 < u.im

/-- Equality holds in the integral order, hence also under real evaluation. -/
def FundamentalSquare : Prop :=
  ∀ D : ℤ, 0 < D → ¬IsSquare D →
    ∀ m p : IntegralQuadratic D, LeastNegative D m → LeastPositive D p → p = m ^ 2

def NegativeParametrization : Prop :=
  ∀ D : ℤ, 0 < D → ¬IsSquare D →
    ∀ m p : IntegralQuadratic D, LeastNegative D m → LeastPositive D p →
    ∀ x y : ℤ, 0 < x → 0 < y → x ^ 2 - D * y ^ 2 = -1 →
      ∃! j : ℕ, realValue D (⟨x, y⟩ : IntegralQuadratic D) =
        realValue D m * (realValue D p) ^ j

/-- Includes j=0, whose integral value is the least negative unit itself. -/
def NegativeProducts : Prop :=
  ∀ D : ℤ, 0 < D → ¬IsSquare D →
    ∀ m p : IntegralQuadratic D, LeastNegative D m → LeastPositive D p →
    ∀ j : ℕ, norm (m * p ^ j) = -1 ∧
      0 < (m * p ^ j).re ∧ 0 < (m * p ^ j).im ∧
      realValue D (m * p ^ j) = realValue D m * (realValue D p) ^ j

def NegativeSolutionSet : Prop :=
  ∀ D : ℤ, 0 < D → ¬IsSquare D →
    ∀ m p : IntegralQuadratic D, LeastNegative D m → LeastPositive D p →
      {r : ℝ | ∃ x y : ℤ, 0 < x ∧ 0 < y ∧ x ^ 2 - D * y ^ 2 = -1 ∧
        r = (x : ℝ) + y * Real.sqrt (D : ℝ)} =
      {r : ℝ | ∃ j : ℕ, r = realValue D m * (realValue D p) ^ j}

end P203Specs.Ch06.NegativePellSolutions
