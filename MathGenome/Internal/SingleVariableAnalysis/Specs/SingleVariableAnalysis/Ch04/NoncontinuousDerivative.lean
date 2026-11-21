import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
Independent specification of K03.04.noncontinuous_derivative (paper.tex:769–780).
All derivatives are with respect to a real variable. The explicit zero branch
fixes the value at the origin; no continuity of the derivative is assumed.
The sampling identity is stated only for positive natural indices, as in the
manuscript, and its approach to zero is a separate obligation.
-/
namespace Specs.SingleVariableAnalysis.Ch04.NoncontinuousDerivative

open scoped Topology

abbrev exampleFunctionType := ℝ → ℝ
noncomputable def exampleFunctionValue : exampleFunctionType :=
  fun x => if x = 0 then 0 else x ^ 2 * Real.sin (1 / x)

abbrev samplePointType := ℕ → ℝ
noncomputable def samplePointValue : samplePointType :=
  fun n => 1 / (2 * Real.pi * (n : ℝ))

def derivativeAtZero : Prop := HasDerivAt exampleFunctionValue 0 0

def derivativeAway : Prop :=
  ∀ x : ℝ, x ≠ 0 → HasDerivAt exampleFunctionValue
    (2 * x * Real.sin (1 / x) - Real.cos (1 / x)) x

def differentiableEverywhere : Prop := Differentiable ℝ exampleFunctionValue

def derivAtZero : Prop := deriv exampleFunctionValue 0 = 0

def derivAway : Prop :=
  ∀ x : ℝ, x ≠ 0 → deriv exampleFunctionValue x =
    2 * x * Real.sin (1 / x) - Real.cos (1 / x)

def samplePositive : Prop := ∀ n : ℕ, 0 < n → 0 < samplePointValue n

def sampleTendsToZero : Prop :=
  Filter.Tendsto samplePointValue Filter.atTop (𝓝 (0 : ℝ))

def derivAtSample : Prop :=
  ∀ n : ℕ, 0 < n → deriv exampleFunctionValue (samplePointValue n) = -1

def derivativeDiscontinuous : Prop := ¬ ContinuousAt (deriv exampleFunctionValue) 0

def notContDiffAtOne : Prop := ¬ ContDiffAt ℝ 1 exampleFunctionValue 0

end Specs.SingleVariableAnalysis.Ch04.NoncontinuousDerivative
