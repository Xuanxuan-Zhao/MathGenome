import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.LogIntegral
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SequenceLimit
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! K03.17.harmonic, paper.tex:4482–4498: existence of Euler's constant.
`harmonicSumValue n` is exactly H_n, with n terms, and H_0 = 0.
The limit sequence is shifted by one to use only the source's positive indices.
All integral values below require proper Darboux integrability. The logarithm
is the shared inverse of the factorial-series exponential. The later Bernoulli
corrections are a separate obligation. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch17.EulerConstant
open scoped BigOperators
open Ch07.LogConstruction Ch08.Integral Ch01.SequenceLimit

def harmonicSumType : Type := ℕ → ℝ
def harmonicSumValue : harmonicSumType :=
  fun n => ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)

def eulerConstantType : Type := ℝ
def eulerConstantValue : eulerConstantType :=
  (show ℝ from sInf (Set.range (fun n : ℕ => harmonicSumValue (n+1) - seriesLogValue ((n : ℝ)+1))))

/-- Both strict rectangle bounds, together with the proper integral identity
and the equivalent log(1+1/x) expression. -/
def logIncrementBounds : Prop :=
  ∀ x : ℝ, 1 ≤ x →
    ∃ h : realIntegrableValue (fun t => 1/t) x (x+1),
      realIntegralValue _ h = seriesLogValue (x+1) - seriesLogValue x ∧
      1/(x+1) < realIntegralValue _ h ∧ realIntegralValue _ h < 1/x ∧
      seriesLogValue (1+1/x) = seriesLogValue (x+1) - seriesLogValue x

def harmonicLogLowerBound : Prop :=
  ∀ n : ℕ, seriesLogValue ((n : ℝ)+1) ≤ harmonicSumValue n

def harmonicLogPositive : Prop :=
  ∀ n : ℕ, 1 ≤ n → 0 < harmonicSumValue n - seriesLogValue (n : ℝ)

def harmonicLogStep : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    harmonicSumValue (n+1) - seriesLogValue ((n : ℝ)+1) <
      harmonicSumValue n - seriesLogValue (n : ℝ)

def harmonicLogAntitone : Prop :=
  AntitoneOn (fun n : ℕ => harmonicSumValue n - seriesLogValue (n : ℝ)) (Set.Ici 1)

def harmonicLogConvergence : Prop :=
  realSequenceConvergesValue
    (fun n : ℕ => harmonicSumValue (n+1) - seriesLogValue ((n : ℝ)+1))
    eulerConstantValue

def harmonicLogLimitExists : Prop :=
  ∃ γ : ℝ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n → |harmonicSumValue n - seriesLogValue (n : ℝ) - γ| < ε

end Specs.SingleVariableAnalysis.Ch17.EulerConstant
