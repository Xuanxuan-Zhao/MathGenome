import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.EulerConstant
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.EmBound

/-! K03.17.harmonic, paper.tex:4482–4512. All indices n below are positive.
The logarithm, harmonic sum, Euler constant, Bernoulli numbers and unit-interval
maxima are exactly the shared objects. The final estimates use explicit bounds,
equivalently big-O along the positive integer sequence. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch17.Harmonic
open scoped BigOperators
open EulerConstant EmBound Ch07.LogConstruction
open Specs.SingleVariableAnalysis.Ch17.Bernoulli

/-- The first m Bernoulli corrections, indexed by r+1 = 1,…,m. -/
def correction (m n : ℕ) : ℝ :=
  ∑ r ∈ Finset.range m,
    bernoulliNumberValue (2 * (r+1)) / ((2 * (r+1) : ℕ) * (n : ℝ) ^ (2 * (r+1)))

/-- The uniquely determined remainder in the stated finite expansion. -/
def error (m n : ℕ) : ℝ := harmonicSumValue n -
  (seriesLogValue n + (show ℝ from eulerConstantValue) + 1 / (2 * (n : ℝ)) - correction m n)

def harmonicExpansion : Prop := ∀ (m : ℕ), 1 ≤ m → ∀ (n : ℕ), 1 ≤ n →
  harmonicSumValue n = seriesLogValue n + (show ℝ from eulerConstantValue) + 1 / (2 * (n : ℝ)) -
    correction m n + error m n ∧
  |error m n| ≤ bernoulliMaximumValue (2*m) / ((2*m : ℕ) * (n : ℝ) ^ (2*m))

/-- One additional correction gives order n^(-2(m+1)) after m displayed terms.
The finite constant is uniform in all positive integer n, and may depend on m. -/
def harmonicControlledRemainder : Prop := ∀ m : ℕ,
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
    |error m n| ≤ C / (n : ℝ) ^ (2 * (m+1))

/-- The explicit formula in the proposition, with the meaning of O(n^(-6))
spelled out as a uniform bound on a tail (in fact on every positive index). -/
def harmonicSixthOrder : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
  |harmonicSumValue n - (seriesLogValue n + (show ℝ from eulerConstantValue) + 1/(2*(n : ℝ)) -
    1/(12*(n : ℝ)^2) + 1/(120*(n : ℝ)^4))| ≤ C / (n : ℝ)^6

end Specs.SingleVariableAnalysis.Ch17.Harmonic
