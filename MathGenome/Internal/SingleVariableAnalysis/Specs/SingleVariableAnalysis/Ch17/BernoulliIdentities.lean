import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.Bernoulli

/-! K03.17.bernoulli, paper.tex:4417–4432.
Identities for the already normalized real Bernoulli polynomials. Natural
powers use `x ^ 0 = 1`, including at zero; `range N` means 0 through N−1.
These statements require no hypotheses beyond their displayed index bounds.
-/
namespace Specs.SingleVariableAnalysis.Ch17.BernoulliIdentities
open Ch17.Bernoulli
open scoped BigOperators

/-- The values at the ends of the unit interval agree from index two onward. -/
def bernoulliEndpoints : Prop := ∀ n : ℕ, 2 ≤ n →
  (bernoulliPolynomialValue n).eval 1 = (bernoulliPolynomialValue n).eval 0

/-- Reflection holds for every index and every real argument. -/
def bernoulliReflection : Prop := ∀ (n : ℕ) (x : ℝ),
  (bernoulliPolynomialValue n).eval (1 - x) =
    (-1 : ℝ) ^ n * (bernoulliPolynomialValue n).eval x

/-- Odd Bernoulli numbers vanish, with the exceptional first number excluded. -/
def bernoulliOddNumber : Prop := ∀ n : ℕ, 3 ≤ n → Odd n →
  bernoulliNumberValue n = 0

/-- The discrete difference identity holds at every real argument. -/
def bernoulliDifference : Prop := ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ,
  (bernoulliPolynomialValue n).eval (x + 1) -
    (bernoulliPolynomialValue n).eval x = (n : ℝ) * x ^ (n - 1)

/-- Includes both the empty sum and the sum of zeroth powers. -/
def bernoulliPowerSum : Prop := ∀ p N : ℕ,
  (∑ k ∈ Finset.range N, (k : ℝ) ^ p) =
    ((bernoulliPolynomialValue (p + 1)).eval (N : ℝ) -
      (bernoulliPolynomialValue (p + 1)).eval 0) / ((p : ℝ) + 1)

end Specs.SingleVariableAnalysis.Ch17.BernoulliIdentities
