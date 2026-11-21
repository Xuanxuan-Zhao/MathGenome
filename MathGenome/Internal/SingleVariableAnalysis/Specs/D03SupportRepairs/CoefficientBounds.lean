import MathGenome.Internal.SingleVariableAnalysis.Specs.D03SupportRepairs.FiniteBinomialIdentities

/-! Independent specifications of the global coefficient estimates and the
complete first theorem of the source. -/

noncomputable section
open scoped BigOperators

namespace D03SupportRepairs.Specs

/-- Both coefficient inequalities, with no upper restriction on j. -/
def coefficientBoundsType : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ (j : ℕ),
    0 ≤ bValue N j ∧ bValue N j ≤ invFactorialValue j

/-- The full finite representation, source-range product identity, and global
coefficient bounds, all for every positive row. -/
def finiteRepresentationAndCoefficientBoundsType : Prop :=
  ∀ (N : ℕ), 1 ≤ N →
    (uValue N = ∑ j ∈ Finset.range (N + 1), bValue N j) ∧
    (∀ (j : ℕ), j ≤ N →
      bValue N j = invFactorialValue j *
        ∏ ℓ ∈ Finset.range j, (1 - (ℓ : ℝ) / (N : ℝ))) ∧
    (∀ (j : ℕ), 0 ≤ bValue N j ∧ bValue N j ≤ invFactorialValue j)

end D03SupportRepairs.Specs
