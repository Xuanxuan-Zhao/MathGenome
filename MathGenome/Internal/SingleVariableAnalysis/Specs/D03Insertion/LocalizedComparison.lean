import MathGenome.Internal.SingleVariableAnalysis.Specs.D03Insertion.CellLengthSums
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic

/-! The comparison is stated for real normed spaces, hence in particular for
both real and complex valued functions. No regularity of the function is required. -/
namespace D03Insertion.Specification

def localized_tagged_sum_comparisonType : Prop :=
  ∀ {K : Type} [NormedAddCommGroup K] [NormedSpace ℝ K]
    {a b : ℝ} (_hab : a < b) {s n t : ℕ}
    {p : Fin (s + 1) → ℝ} {q : Fin (n + 1) → ℝ} {r : Fin (t + 1) → ℝ},
    ValidPartition a b p → ValidPartition a b q → ValidPartition a b r →
    nodes r = nodes p ∪ nodes q →
    ∀ (f : Set.Icc a b → K) (M : ℝ), 0 ≤ M →
    (∀ x, ‖f x‖ ≤ M) →
    ∀ ξ : Fin n → Set.Icc a b, Legal q ξ →
    ∃ ζ : Fin t → Set.Icc a b,
      Legal r ζ ∧
      (∀ i, i ∉ marked p q → ∀ j,
        left r j = left q i → right r j = right q i → ζ j = ξ i) ∧
      ‖taggedSum f q ξ - taggedSum f r ζ‖ ≤
        2 * M * (∑ i ∈ marked p q, width q i)

end D03Insertion.Specification
