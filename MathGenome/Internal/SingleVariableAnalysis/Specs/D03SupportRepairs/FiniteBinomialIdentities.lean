import MathGenome.Internal.SingleVariableAnalysis.Specs.D03SupportRepairs.BinomialQuantities

/-! Independent propositions for the two finite binomial identities. -/

noncomputable section
open scoped BigOperators

namespace D03SupportRepairs.Specs

/-- The complete binomial expansion of a positive row. -/
def finiteRepresentationType : Prop :=
  ∀ (N : ℕ), 1 ≤ N →
    uValue N = ∑ j ∈ Finset.range (N + 1), bValue N j

/-- The coefficient product formula, including the empty product at j = 0. -/
def coefficientProductType : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ (j : ℕ), j ≤ N →
    bValue N j = invFactorialValue j *
      ∏ ℓ ∈ Finset.range j, (1 - (ℓ : ℝ) / (N : ℝ))

end D03SupportRepairs.Specs
