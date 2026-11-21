import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Data.Nat.Factorial.Basic

/-! Independent statements for the logarithmic part of K03.17.stirling,
paper.tex:4510–4528. All asymptotic filters are natural numbers at infinity;
exact formulas are restricted to positive indices. The normalization constant
is left unspecified, as required by this goal. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch17.StirlingLogError
open Filter
open scoped Topology

def logSequence (n : ℕ) : ℝ :=
  Real.log (n.factorial : ℝ) - ((n : ℝ) + 1/2) * Real.log n + n

def sequenceType : Type := ℕ → ℝ
def sequenceValue : sequenceType := logSequence

def incrementIdentity : Prop := ∀ n : ℕ, 1 ≤ n →
  logSequence (n+1) - logSequence n =
    1 - ((n : ℝ) + 1/2) * Real.log (1 + 1/(n : ℝ))

def incrementExpansion : Prop := Asymptotics.IsBigO atTop
  (fun n : ℕ => logSequence (n+1) - logSequence n + 1/(12*(n : ℝ)^2))
  (fun n : ℕ => (n : ℝ)⁻¹ ^ 3)

def absoluteIncrements : Prop :=
  Summable (fun n : ℕ => |logSequence (n+2) - logSequence (n+1)|)

/-- The absolute tail starting with s_(n+1)-s_n has the stated inverse-linear bound. -/
def absoluteTailBound : Prop := ∃ c : ℝ,
  Tendsto logSequence atTop (𝓝 c) ∧ ∀ n : ℕ, 1 ≤ n →
    HasSum (fun k : ℕ => |logSequence (n+k+1) - logSequence (n+k)|) (logSequence n-c) ∧
    0 ≤ logSequence n-c ∧ logSequence n-c ≤ 1/(12*(n : ℝ))

def logarithmicError : Prop := ∃ c : ℝ,
  Tendsto logSequence atTop (𝓝 c) ∧
  Asymptotics.IsBigO atTop (fun n => logSequence n - c) (fun n : ℕ => (n : ℝ)⁻¹)

/-- `exp(O(1/n))` is made explicit by the actual remainder `logSequence n - c`.
The same c is the limit and gives the positive multiplicative constant exp c. -/
def factorialForm : Prop := ∃ c : ℝ,
  Tendsto logSequence atTop (𝓝 c) ∧
  Asymptotics.IsBigO atTop (fun n => logSequence n - c) (fun n : ℕ => (n : ℝ)⁻¹) ∧
  0 < Real.exp c ∧ ∀ n : ℕ, 1 ≤ n →
    (n.factorial : ℝ) = Real.exp c *
      (n : ℝ)^((n : ℝ)+1/2) * Real.exp (-(n : ℝ)) * Real.exp (logSequence n - c)
end Specs.SingleVariableAnalysis.Ch17.StirlingLogError
