import MathGenome.Internal.SingleVariableAnalysis.Specs.D03SupportRepairs.BinomialQuantities

/-! Shared quantities for the binomial prefix and uniform tail comparison.

The definitions are total at N = 0. Later assertions about a positive binomial
row must retain the hypothesis 1 ≤ N. No summability assumption is introduced.
-/

noncomputable section
open scoped BigOperators

namespace D03SupportRepairs

/-- The binomial sequence, totalized at zero. -/
def u (N : ℕ) : ℝ :=
  (1 + 1 / (N : ℝ)) ^ N

/-- The normalized canonical binomial coefficient. -/
def b (N j : ℕ) : ℝ :=
  (Nat.choose N j : ℝ) / (N : ℝ) ^ j

/-- The prefix through the inclusive cutoff J. -/
def «prefix» (N J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1), b N j

/-- The real inverse factorial. -/
def invFactorial (j : ℕ) : ℝ :=
  1 / (Nat.factorial j : ℝ)

/-- The source geometric majorant term. -/
def geomTerm (j : ℕ) : ℝ :=
  (2 : ℝ) * (1 / 2 : ℝ) ^ j

/-- The actual inverse-factorial series restricted to j > J. -/
def factorialTail (J : ℕ) : ℝ :=
  ∑' j : ℕ, if J < j then invFactorial j else 0

/-- The actual geometric series restricted to j > J. -/
def geometricTail (J : ℕ) : ℝ :=
  ∑' j : ℕ, if J < j then geomTerm j else 0

end D03SupportRepairs
