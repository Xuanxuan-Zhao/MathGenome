import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch06.PellUnits

/-! Independent statements for paper.tex, Theorem nt:D07 (2713–2736).
The chapter assumes only that the integer D is positive and nonsquare.
All elements below belong to the integer-coefficient order, not a larger
ring of integers. `Pell.Solution₁` is used only for its norm-one group. -/
namespace P203Specs.Ch06.FundamentalPellSolution
open P203Specs.Ch06.PellUnits

/-- Minimality is in the source's real ordering, among every norm-one
integer-coefficient element whose real value exceeds one. -/
def LeastPositive (D : ℤ) (u : IntegralQuadratic D) : Prop :=
  norm u = 1 ∧ 1 < realValue D u ∧
    ∀ v : IntegralQuadratic D, norm v = 1 → 1 < realValue D v →
      realValue D u ≤ realValue D v

def FundamentalBridge : Prop :=
  ∀ (D : ℤ), 0 < D → ¬IsSquare D → ∀ a : Pell.Solution₁ D,
    Pell.IsFundamental a ↔ LeastPositive D (a : IntegralQuadratic D)

def FundamentalExists : Prop :=
  ∀ (D : ℤ), 0 < D → ¬IsSquare D →
    ∃! u : IntegralQuadratic D, LeastPositive D u

def LeastCoordinates : Prop :=
  ∀ (D : ℤ), 0 < D → ∀ u : IntegralQuadratic D, LeastPositive D u →
    IsUnit u ∧ 0 < u.re ∧ 0 < u.im

/-- Every positive integral Pell pair has one and only one strictly positive
natural exponent; these are exactly the positive integers in the source. -/
def PositiveParametrization : Prop :=
  ∀ (D : ℤ), 0 < D → ¬IsSquare D →
    ∀ u : IntegralQuadratic D, LeastPositive D u →
    ∀ x y : ℤ, 0 < x → 0 < y → x ^ 2 - D * y ^ 2 = 1 →
      ∃! j : ℕ, 1 ≤ j ∧
        realValue D (⟨x, y⟩ : IntegralQuadratic D) = (realValue D u) ^ j

/-- Conversely, each strictly positive power has positive integral
coordinates and norm one, and its real evaluation is the required power. -/
def PositivePowers : Prop :=
  ∀ (D : ℤ), 0 < D → ¬IsSquare D →
    ∀ u : IntegralQuadratic D, LeastPositive D u →
    ∀ j : ℕ, 1 ≤ j →
      norm (u ^ j) = 1 ∧ 0 < (u ^ j).re ∧ 0 < (u ^ j).im ∧
        realValue D (u ^ j) = (realValue D u) ^ j

/-- This quantifies over every integral norm-one element of positive real
value, including values equal to or below one. Such elements are units by
the shared norm criterion. Integer exponents refer to real integer powers. -/
def IntegerParametrization : Prop :=
  ∀ (D : ℤ), 0 < D → ¬IsSquare D →
    ∀ u : IntegralQuadratic D, LeastPositive D u →
    ∀ v : IntegralQuadratic D, norm v = 1 → 0 < realValue D v →
      ∃! j : ℤ, realValue D v = (realValue D u) ^ j

/-- Every integer power is realized in the original order, with the exact
three exponent ranges. In particular exponent zero is the identity, and
negative exponents give positive values below one. -/
def IntegerPowers : Prop :=
  ∀ (D : ℤ), 0 < D → ¬IsSquare D →
    ∀ u : IntegralQuadratic D, LeastPositive D u →
    ∀ j : ℤ, ∃ v : IntegralQuadratic D,
      norm v = 1 ∧ IsUnit v ∧ realValue D v = (realValue D u) ^ j ∧
      0 < realValue D v ∧ (v = 1 ↔ j = 0) ∧
      (realValue D v < 1 ↔ j < 0) ∧
      (realValue D v = 1 ↔ j = 0) ∧
      (1 < realValue D v ↔ 0 < j)

end P203Specs.Ch06.FundamentalPellSolution
