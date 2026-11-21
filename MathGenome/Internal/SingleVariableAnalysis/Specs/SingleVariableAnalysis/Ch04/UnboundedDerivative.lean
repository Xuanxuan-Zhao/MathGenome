import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Sqrt

/-! Independent specification of K03.04.unbounded_derivative (paper.tex:776–785)
and the analytic example reused at K03.09.derivative_not_integrable.
The sequence is indexed by naturals, with the displayed evaluation restricted
to positive indices, as in the manuscript. Riemann nonintegrability is a
separate downstream obligation. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch04.UnboundedDerivative

def functionType := ℝ → ℝ
def functionValue : functionType :=
  fun x => if x = 0 then 0 else x ^ 2 * Real.sin (1 / x ^ 2)

def sequenceType := ℕ → ℝ
def sequenceValue : sequenceType := fun n => 1 / Real.sqrt (2 * Real.pi * n)

def hasDerivAtZero : Prop := HasDerivAt functionValue 0 0
def hasDerivAtNonzero : Prop := ∀ x : ℝ, x ≠ 0 →
  HasDerivAt functionValue
    (2 * x * Real.sin (1 / x ^ 2) - (2 / x) * Real.cos (1 / x ^ 2)) x
def differentiable : Prop := Differentiable ℝ functionValue
def derivZero : Prop := deriv functionValue 0 = 0
def derivNonzero : Prop := ∀ x : ℝ, x ≠ 0 →
  deriv functionValue x =
    2 * x * Real.sin (1 / x ^ 2) - (2 / x) * Real.cos (1 / x ^ 2)
def sequencePositive : Prop := ∀ n : ℕ, 0 < n → 0 < sequenceValue n
def sequenceTendstoZero : Prop :=
  Filter.Tendsto sequenceValue Filter.atTop (nhds 0)
def derivSequence : Prop := ∀ n : ℕ, 0 < n →
  deriv functionValue (sequenceValue n) = -2 * Real.sqrt (2 * Real.pi * n)
def derivSequenceTendsto : Prop :=
  Filter.Tendsto (fun n => deriv functionValue (sequenceValue n))
    Filter.atTop Filter.atBot
def locallyUnboundedBelow : Prop := ∀ δ : ℝ, 0 < δ → ∀ B : ℝ,
  ∃ x : ℝ, 0 < x ∧ x < δ ∧ deriv functionValue x < B
def locallyUnbounded : Prop := ∀ δ : ℝ, 0 < δ → ∀ M : ℝ,
  ∃ x : ℝ, 0 < |x| ∧ |x| < δ ∧ M < |deriv functionValue x|

end Specs.SingleVariableAnalysis.Ch04.UnboundedDerivative
