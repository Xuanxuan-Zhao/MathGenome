import MathGenome.Internal.SingleVariableAnalysis.Specs.D03SupportRepairs.BinomialQuantities

/-! Independent propositions for the limits with fixed coefficient and prefix indices. -/

noncomputable section
open scoped BigOperators Topology

namespace D03SupportRepairs.Specs

/-- Each fixed coefficient tends to the corresponding inverse factorial along positive rows. -/
def coefficientLimitType : Prop :=
  ∀ j : ℕ, Filter.Tendsto (fun n : ℕ => bValue (n + 1) j)
    Filter.atTop (𝓝 (invFactorialValue j))

/-- Each fixed inclusive prefix tends to the finite sum of inverse factorials. -/
def fixedPrefixLimitType : Prop :=
  ∀ J : ℕ, Filter.Tendsto (fun n : ℕ => prefixValue (n + 1) J)
    Filter.atTop (𝓝 (∑ j ∈ Finset.range (J + 1), invFactorialValue j))

end D03SupportRepairs.Specs
