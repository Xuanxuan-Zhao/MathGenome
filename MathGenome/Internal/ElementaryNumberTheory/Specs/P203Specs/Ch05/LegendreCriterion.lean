import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.Convergents

/-! Legendre's criterion, paper.tex, cor:nt-legendre (lines 2231–2255).
The positive denominator and gcd condition fix the reduced integer pair,
and the conclusion identifies that pair with the canonical integer recurrences.
-/
namespace P203Specs

def LegendreCriterion : Prop :=
  ∀ (x : ℝ), Irrational x → ∀ (p q : ℤ), 0 < q → Int.gcd p q = 1 →
    |x - (p : ℝ) / (q : ℝ)| < 1 / (2 * (q : ℝ) ^ 2) →
    ∃ n : ℕ, p = convergentNumerator x n ∧ q = convergentDenominator x n

end P203Specs
