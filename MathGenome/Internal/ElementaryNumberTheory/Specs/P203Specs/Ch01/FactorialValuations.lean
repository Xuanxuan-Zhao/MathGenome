import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch01.FactorizationValuations
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
Independent specification of `paper.tex`, Theorem 1.5 (`nt:A04`, lines 230–265).
For nonnegative numerators and positive denominators, natural division is the
floor in the source. Sums over `Ico 1 b` contain exactly the positive exponents
below a cutoff. The formulas hold for every cutoff with `n < p^b`; the cutoff
statement proves such cutoffs exist and that all omitted summands are zero.
The valuation is the canonical extended valuation from Theorem 1.3, explicitly
finite here, and its `toNat` is therefore its finite exponent.
-/
namespace P203Specs.Ch01

/-- Integer subtraction, rather than truncated natural subtraction. -/
def binomialFloorDifference (p n k j : ℕ) : ℤ :=
  (n / p ^ j : ℕ) - (k / p ^ j : ℕ) - ((n - k) / p ^ j : ℕ)

def FactorialValuationFormula : Prop :=
  ∀ p : ℕ, p.Prime → ∀ n b : ℕ, n < p ^ b →
    primeValuation p (n.factorial : ℤ) ≠ ⊤ ∧
    (primeValuation p (n.factorial : ℤ)).toNat =
      ∑ j ∈ Finset.Ico 1 b, n / p ^ j

def BinomialValuationFormula : Prop :=
  ∀ p : ℕ, p.Prime → ∀ n k : ℕ, k ≤ n →
    ∀ b : ℕ, n < p ^ b →
      primeValuation p (n.choose k : ℤ) ≠ ⊤ ∧
      ((primeValuation p (n.choose k : ℤ)).toNat : ℤ) =
        ∑ j ∈ Finset.Ico 1 b, binomialFloorDifference p n k j

def BinomialFloorDifferenceZeroOrOne : Prop :=
  ∀ p : ℕ, p.Prime → ∀ n k : ℕ, k ≤ n → ∀ j : ℕ,
    binomialFloorDifference p n k j = 0 ∨
    binomialFloorDifference p n k j = 1

def ValuationSumCutoff : Prop :=
  ∀ p : ℕ, p.Prime → ∀ n : ℕ,
    (∃ b : ℕ, n < p ^ b) ∧
    ∀ j : ℕ, n < p ^ j →
      n / p ^ j = 0 ∧
      ∀ k : ℕ, k ≤ n → binomialFloorDifference p n k j = 0

end P203Specs.Ch01
