import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch06.NegativePellSolutions

/-! The substantive examples concluding Chapter 6, paper.tex:2769–2771.
Periods and digits use the canonical algorithm. Minimality is in the real
ordering on the original integer-coefficient order. -/
namespace P203Specs.Ch06.PellExamples
open P203Specs
open PellUnits FundamentalPellSolution NegativePellSolutions

def twoMinus : IntegralQuadratic 2 := ⟨1, 1⟩
def twoPlus : IntegralQuadratic 2 := ⟨3, 2⟩
def threePlus : IntegralQuadratic 3 := ⟨2, 1⟩

def SqrtTwoExpansion : Prop :=
  sqrtPeriod 2 = 1 ∧
  partialQuotient (Real.sqrt 2) 0 = some 1 ∧
  ∀ n : ℕ, partialQuotient (Real.sqrt 2) (n + 1) = some 2

def SqrtThreeExpansion : Prop :=
  sqrtPeriod 3 = 2 ∧
  partialQuotient (Real.sqrt 3) 0 = some 1 ∧
  ∀ n : ℕ, partialQuotient (Real.sqrt 3) (2 * n + 1) = some 1 ∧
    partialQuotient (Real.sqrt 3) (2 * n + 2) = some 2

def TwoFundamentalUnits : Prop :=
  LeastNegative 2 twoMinus ∧ LeastPositive 2 twoPlus ∧
  realValue 2 twoMinus = 1 + Real.sqrt 2 ∧
  realValue 2 twoPlus = 3 + 2 * Real.sqrt 2 ∧ twoPlus = twoMinus ^ 2

def ThreeFundamentalUnit : Prop :=
  LeastPositive 3 threePlus ∧ realValue 3 threePlus = 2 + Real.sqrt 3 ∧
  ¬ ∃ x y : ℤ, x ^ 2 - 3 * y ^ 2 = -1

/-- The full positive-solution theorem specialized to the displayed generator,
including positive real units below one and the identity. -/
def PositiveClassification (D : ℤ) (u : IntegralQuadratic D) : Prop :=
  (∀ x y : ℤ, 0 < x → 0 < y → x ^ 2 - D * y ^ 2 = 1 →
    ∃! j : ℕ, 1 ≤ j ∧ realValue D (⟨x, y⟩ : IntegralQuadratic D) = realValue D u ^ j) ∧
  (∀ j : ℕ, 1 ≤ j → norm (u ^ j) = 1 ∧ 0 < (u ^ j).re ∧ 0 < (u ^ j).im ∧
    realValue D (u ^ j) = realValue D u ^ j) ∧
  (∀ v : IntegralQuadratic D, norm v = 1 → 0 < realValue D v →
    ∃! j : ℤ, realValue D v = realValue D u ^ j) ∧
  (∀ j : ℤ, ∃ v : IntegralQuadratic D, norm v = 1 ∧ IsUnit v ∧
    realValue D v = realValue D u ^ j ∧ 0 < realValue D v ∧
    (v = 1 ↔ j = 0) ∧ (realValue D v < 1 ↔ j < 0) ∧
    (realValue D v = 1 ↔ j = 0) ∧ (1 < realValue D v ↔ 0 < j))

def TwoSolutionClassification : Prop :=
  PositiveClassification 2 twoPlus ∧
  (∀ x y : ℤ, 0 < x → 0 < y → x ^ 2 - 2 * y ^ 2 = -1 →
    ∃! j : ℕ, realValue 2 (⟨x, y⟩ : IntegralQuadratic 2) =
      realValue 2 twoMinus * realValue 2 twoPlus ^ j) ∧
  (∀ j : ℕ, norm (twoMinus * twoPlus ^ j) = -1 ∧
    0 < (twoMinus * twoPlus ^ j).re ∧ 0 < (twoMinus * twoPlus ^ j).im ∧
    realValue 2 (twoMinus * twoPlus ^ j) = realValue 2 twoMinus * realValue 2 twoPlus ^ j)

def ThreeSolutionClassification : Prop := PositiveClassification 3 threePlus

end P203Specs.Ch06.PellExamples
