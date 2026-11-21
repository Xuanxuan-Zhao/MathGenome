import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.RealPowers

/-!
Independent statements for K03.05.inequalities, paper.tex:962–978.
The functions are the shared factorial-series exponential, its inverse on
positive arguments, and the corresponding real powers. Families are indexed
by arbitrary finite sets, with no restriction on zero weights. Normalization
excludes an empty family without an additional nonemptiness hypothesis.
-/

noncomputable section
namespace Specs.SingleVariableAnalysis.Ch05.Inequalities
open scoped BigOperators
open Ch07.ExpConstruction Ch07.LogConstruction Ch07.RealPowers

/-- The supporting line at zero, on the whole real line. -/
def exponentialLowerBound : Prop :=
  ∀ x : ℝ, 1 + x ≤ realSeriesExpValue x

/-- Equality in the exponential bound holds exactly at zero. -/
def exponentialEquality : Prop :=
  ∀ x : ℝ, realSeriesExpValue x = 1 + x ↔ x = 0

/-- The logarithmic bound has positive domain. -/
def logarithmUpperBound : Prop :=
  ∀ x : ℝ, 0 < x → seriesLogValue x ≤ x - 1

/-- Equality in the logarithmic bound holds exactly at one. -/
def logarithmEquality : Prop :=
  ∀ x : ℝ, 0 < x → (seriesLogValue x = x - 1 ↔ x = 1)

/-- Weighted AM–GM for positive inputs and nonnegative normalized weights. -/
def weightedArithmeticGeometric : Prop :=
  ∀ {ι : Type*} (s : Finset ι) (w a : ι → ℝ),
    (∀ j ∈ s, 0 ≤ w j) → (∑ j ∈ s, w j) = 1 →
    (∀ j ∈ s, 0 < a j) →
    (∏ j ∈ s, realPowerValue (a j) (w j)) ≤ ∑ j ∈ s, w j * a j

/-- Only the inputs carrying positive weights must coincide. -/
def weightedArithmeticGeometricEquality : Prop :=
  ∀ {ι : Type*} (s : Finset ι) (w a : ι → ℝ),
    (∀ j ∈ s, 0 ≤ w j) → (∑ j ∈ s, w j) = 1 →
    (∀ j ∈ s, 0 < a j) →
    ((∏ j ∈ s, realPowerValue (a j) (w j)) = ∑ j ∈ s, w j * a j ↔
      ∀ j ∈ s, 0 < w j → ∀ k ∈ s, 0 < w k → a j = a k)

end Specs.SingleVariableAnalysis.Ch05.Inequalities
