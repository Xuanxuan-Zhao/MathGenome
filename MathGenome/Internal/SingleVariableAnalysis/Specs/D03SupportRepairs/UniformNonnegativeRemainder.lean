import MathGenome.Internal.SingleVariableAnalysis.Specs.D03SupportRepairs.BinomialQuantities

/-! Independent propositions for the complete uniform remainder theorem. -/

open scoped Topology

namespace D03SupportRepairs.Specs

/-- Every positive row and every natural cutoff satisfy the same actual tail
bounds, and the geometric tails tend to zero. -/
def uniformNonnegativeRemainderType : Prop :=
  (∀ (N : ℕ), 1 ≤ N → ∀ (J : ℕ),
    0 ≤ uValue N - prefixValue N J ∧
    uValue N - prefixValue N J ≤ factorialTailValue J ∧
    factorialTailValue J ≤ geometricTailValue J) ∧
  Filter.Tendsto geometricTailValue Filter.atTop (nhds (0 : ℝ))

/-- The remainder vanishes at and beyond the last coefficient of a positive row. -/
def remainderEqZeroType : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ (J : ℕ), N ≤ J →
    uValue N - prefixValue N J = 0

end D03SupportRepairs.Specs
