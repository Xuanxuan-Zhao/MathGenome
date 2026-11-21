import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.LegendreGauss

/-! Theorem 2.8 (`nt:B07`), paper.tex:675–688, with the conventions at
58–65 and the Legendre symbol defined at 634–638. Positive primes are
represented by natural primes; the symbols take values in the integers.
All exponents use natural exact quotients in the source's formulas. -/
namespace P203Specs.Ch02

/-- Quadratic reciprocity for every pair of distinct odd primes. -/
def QuadraticReciprocity : Prop :=
  ∀ (p q : ℕ) [Fact p.Prime] [Fact q.Prime], p ≠ 2 → q ≠ 2 → p ≠ q →
    legendreSymbol (q : ℤ) p * legendreSymbol (p : ℤ) q =
      (-1 : ℤ) ^ (((p - 1) / 2) * ((q - 1) / 2))

/-- The first supplement, in its exact exponent form. -/
def SupplementNegOne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
    legendreSymbol (-1) p = (-1 : ℤ) ^ ((p - 1) / 2)

/-- The second supplement, in its exact exponent form. -/
def SupplementTwo : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
    legendreSymbol 2 p = (-1 : ℤ) ^ ((p ^ 2 - 1) / 8)

end P203Specs.Ch02
