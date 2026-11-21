import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.Convergents

/-! Best approximation of the second kind, paper.tex §nt:E04, lines 2206–2229.
The errors are scaled numerator errors. The integer pair need not be reduced,
and the natural index includes zero. -/
namespace P203Specs

def BestApproximationSecondKind : Prop :=
  ∀ (x : ℝ), Irrational x → ∀ (n : ℕ) (p q : ℤ),
    0 < q → q < convergentDenominator x (n + 1 : ℕ) →
    |(convergentDenominator x n : ℝ) * x - (convergentNumerator x n : ℝ)| ≤
      |(q : ℝ) * x - (p : ℝ)|

def BestApproximationEquality : Prop :=
  ∀ (x : ℝ), Irrational x → ∀ (n : ℕ) (p q : ℤ),
    0 < q → q < convergentDenominator x (n + 1 : ℕ) →
    |(q : ℝ) * x - (p : ℝ)| =
      |(convergentDenominator x n : ℝ) * x - (convergentNumerator x n : ℝ)| →
    (p, q) = (convergentNumerator x n, convergentDenominator x n)

end P203Specs
