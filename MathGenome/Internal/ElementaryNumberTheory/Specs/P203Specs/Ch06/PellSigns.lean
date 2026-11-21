import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch06.SquareRootReturnPoints

/-! `paper.tex`, Theorem nt:D08 (2661–2695): both Pell signs, all positive
solutions, ordering, and least indices. No squarefreeness is assumed. -/
namespace P203Specs

/-- A positive integer solution of the indicated norm equation. -/
def PositivePell (D ε x y : ℤ) : Prop :=
  0 < x ∧ 0 < y ∧ x ^ 2 - D * y ^ 2 = ε

noncomputable def pellValue (D x y : ℤ) : ℝ :=
  (x : ℝ) + (y : ℝ) * Real.sqrt (D : ℝ)

/-- The `k`th return pair, at the source index `k*ℓ-1`. All theorems using
these functions require `k ≥ 1`, so subtraction is at a nonnegative index. -/
noncomputable def pellPeriodNumerator (D : ℤ) (k : ℕ) : ℤ :=
  convergentNumerator (Real.sqrt (D : ℝ)) (((k * sqrtPeriod D : ℕ) : ℤ) - 1)
noncomputable def pellPeriodDenominator (D : ℤ) (k : ℕ) : ℤ :=
  convergentDenominator (Real.sqrt (D : ℝ)) (((k * sqrtPeriod D : ℕ) : ℤ) - 1)

/-- Minimality in the real ordering specified in the paper. -/
def IsLeastPositivePell (D ε p q : ℤ) : Prop :=
  PositivePell D ε p q ∧
    ∀ x y : ℤ, PositivePell D ε x y → pellValue D p q ≤ pellValue D x y

def PellClassification : Prop :=
  ∀ D : ℤ, 0 < D → ¬ IsSquare D → ∀ ε : ℤ, (ε = 1 ∨ ε = -1) →
    ∀ x y : ℤ, 0 < x → 0 < y →
      (x ^ 2 - D * y ^ 2 = ε ↔ ∃ k : ℕ, 1 ≤ k ∧
        x = pellPeriodNumerator D k ∧ y = pellPeriodDenominator D k ∧
        (-1 : ℤ) ^ (k * sqrtPeriod D) = ε)

/-- The return pairs increase strictly in the real ordering, for either sign.
Together with classification this also compares any two solutions of one sign. -/
def PellOrdering : Prop :=
  ∀ D : ℤ, 0 < D → ¬ IsSquare D → ∀ j k : ℕ, 1 ≤ j → 1 ≤ k →
    (pellValue D (pellPeriodNumerator D j) (pellPeriodDenominator D j) <
      pellValue D (pellPeriodNumerator D k) (pellPeriodDenominator D k) ↔ j < k)

/-- The least solution corresponds exactly to the least permitted `k`. -/
def PellLeastIndex : Prop :=
  ∀ D : ℤ, 0 < D → ¬ IsSquare D → ∀ ε : ℤ, (ε = 1 ∨ ε = -1) →
    ∀ k : ℕ, 1 ≤ k → (-1 : ℤ) ^ (k * sqrtPeriod D) = ε →
      (IsLeastPositivePell D ε (pellPeriodNumerator D k) (pellPeriodDenominator D k) ↔
        ∀ j : ℕ, 1 ≤ j → (-1 : ℤ) ^ (j * sqrtPeriod D) = ε → k ≤ j)

def PellFundamentalSigns : Prop :=
  ∀ D : ℤ, 0 < D → ¬ IsSquare D →
    (Even (sqrtPeriod D) →
      IsLeastPositivePell D 1 (pellPeriodNumerator D 1) (pellPeriodDenominator D 1)) ∧
    (Odd (sqrtPeriod D) →
      IsLeastPositivePell D 1 (pellPeriodNumerator D 2) (pellPeriodDenominator D 2)) ∧
    ((∃ x y : ℤ, PositivePell D (-1) x y) ↔ Odd (sqrtPeriod D)) ∧
    (Odd (sqrtPeriod D) →
      IsLeastPositivePell D (-1) (pellPeriodNumerator D 1) (pellPeriodDenominator D 1))

end P203Specs
