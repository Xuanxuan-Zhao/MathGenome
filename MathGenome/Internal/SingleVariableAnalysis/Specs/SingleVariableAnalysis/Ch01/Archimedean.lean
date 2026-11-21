import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Scalar

/-!
Independent propositions for `K03.01.archimedean` (paper.tex:181–191).
The scalar types, coercions, absolute value and topology are canonical.
Natural indices are explicitly positive where a reciprocal is estimated.
-/

namespace Specs.SingleVariableAnalysis.Ch01.Archimedean

open scoped Topology

/-- Every real number is strictly below a positive natural number. -/
def archimedeanBound : Prop :=
  ∀ x : ℝ, ∃ n : ℕ, 0 < n ∧ x < (n : ℝ)

/-- Every nonempty open real interval contains a rational number. -/
def rationalDensity : Prop :=
  ∀ x y : ℝ, x < y → ∃ q : ℚ, x < (q : ℝ) ∧ (q : ℝ) < y

/-- The defining tail inequality for the reciprocal sequence, with positive
threshold and hence with no zero denominator on the asserted tail. -/
def reciprocalTail : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
    ∀ n : ℕ, N ≤ n → |1 / (n : ℝ)| < ε

/-- The standard topological expression of `1/n → 0`.
The initial term at zero has no effect on an `atTop` limit; `reciprocalTail`
also records the source's estimate solely on positive indices. -/
def reciprocalLimit : Prop :=
  Filter.Tendsto (fun n : ℕ => 1 / (n : ℝ)) Filter.atTop (𝓝 (0 : ℝ))

/-- Approximate any real number by a rational with any prescribed positive
absolute error. -/
def rationalApproximation : Prop :=
  ∀ x ε : ℝ, 0 < ε → ∃ q : ℚ, |(q : ℝ) - x| < ε

end Specs.SingleVariableAnalysis.Ch01.Archimedean
