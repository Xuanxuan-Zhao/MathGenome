import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Uniform
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Derivative
import Mathlib.Basic.ENNReal.Real

/-!
K03.12.differentiation, paper.tex:1257–1266, first proof stage.
Ambient functions represent their restrictions to [a,b]; no condition is
imposed outside this interval. All derivatives are over ℝ, also for ℂ values.
The derivative limit is tested only on (a,b). No derivative continuity or
endpoint differentiability is required. Indices n represent source indices n+1.

The supremum estimate uses ℝ≥0∞ so it remains meaningful for every pair of
indices, including pairs with unbounded derivative difference. The finite-bound
estimate is also retained explicitly. The convergence conclusions have exactly
the source hypotheses, without any boundedness hypothesis on early differences.
Continuity and differentiation of the limit are allocated to the subsequent goal.
-/

namespace Specs.SingleVariableAnalysis.Ch12.DerivativeUniformCauchy

open Set

def real_derivative_difference_bound : Prop :=
  ∀ (F : ℕ → ℝ → ℝ) (a b x₀ x M : ℝ) (m n : ℕ),
    a < b → x₀ ∈ Icc a b → x ∈ Icc a b → 0 ≤ M →
    (∀ k, ContinuousOn (F k) (Icc a b)) →
    (∀ k, ∀ t ∈ Ioo a b, DifferentiableAt ℝ (F k) t) →
    (∀ t ∈ Ioo a b, |deriv (F n) t - deriv (F m) t| ≤ M) →
    |F n x - F m x| ≤ |F n x₀ - F m x₀| + (b - a) * M

def real_derivative_difference_sup_estimate : Prop :=
  ∀ (F : ℕ → ℝ → ℝ) (a b x₀ x : ℝ) (m n : ℕ),
    a < b → x₀ ∈ Icc a b → x ∈ Icc a b →
    (∀ k, ContinuousOn (F k) (Icc a b)) →
    (∀ k, ∀ t ∈ Ioo a b, DifferentiableAt ℝ (F k) t) →
    ENNReal.ofReal |F n x - F m x| ≤
      ENNReal.ofReal |F n x₀ - F m x₀| +
        ENNReal.ofReal (b - a) *
          ⨆ t : Ioo a b, ENNReal.ofReal |deriv (F n) t - deriv (F m) t|

def real_derivative_uniform_cauchy : Prop :=
  ∀ (F : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (a b x₀ : ℝ),
    a < b → x₀ ∈ Icc a b →
    (∀ n, ContinuousOn (F n) (Icc a b)) →
    (∀ n, ∀ t ∈ Ioo a b, DifferentiableAt ℝ (F n) t) →
    (∃ L : ℝ, Ch01.SequenceLimit.realSequenceConvergesValue
      (fun n => F n x₀) L) →
    Uniform.realUniformConvergesValue
      (fun n (t : Ioo a b) => deriv (F n) t) (fun t => g t) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      ∀ x ∈ Icc a b, |F n x - F m x| < ε) ∧
    ∃ f : Icc a b → ℝ, Uniform.realUniformConvergesValue
      (fun n (x : Icc a b) => F n x) f

def complex_derivative_difference_bound : Prop :=
  ∀ (F : ℕ → ℝ → ℂ) (a b x₀ x M : ℝ) (m n : ℕ),
    a < b → x₀ ∈ Icc a b → x ∈ Icc a b → 0 ≤ M →
    (∀ k, ContinuousOn (F k) (Icc a b)) →
    (∀ k, ∀ t ∈ Ioo a b, DifferentiableAt ℝ (F k) t) →
    (∀ t ∈ Ioo a b, ‖deriv (F n) t - deriv (F m) t‖ ≤ M) →
    ‖F n x - F m x‖ ≤ ‖F n x₀ - F m x₀‖ + (b - a) * M

def complex_derivative_difference_sup_estimate : Prop :=
  ∀ (F : ℕ → ℝ → ℂ) (a b x₀ x : ℝ) (m n : ℕ),
    a < b → x₀ ∈ Icc a b → x ∈ Icc a b →
    (∀ k, ContinuousOn (F k) (Icc a b)) →
    (∀ k, ∀ t ∈ Ioo a b, DifferentiableAt ℝ (F k) t) →
    ENNReal.ofReal ‖F n x - F m x‖ ≤
      ENNReal.ofReal ‖F n x₀ - F m x₀‖ +
        ENNReal.ofReal (b - a) *
          ⨆ t : Ioo a b, ENNReal.ofReal ‖deriv (F n) t - deriv (F m) t‖

def complex_derivative_uniform_cauchy : Prop :=
  ∀ (F : ℕ → ℝ → ℂ) (g : ℝ → ℂ) (a b x₀ : ℝ),
    a < b → x₀ ∈ Icc a b →
    (∀ n, ContinuousOn (F n) (Icc a b)) →
    (∀ n, ∀ t ∈ Ioo a b, DifferentiableAt ℝ (F n) t) →
    (∃ L : ℂ, Ch01.SequenceLimit.complexSequenceConvergesValue
      (fun n => F n x₀) L) →
    Uniform.complexUniformConvergesValue
      (fun n (t : Ioo a b) => deriv (F n) t) (fun t => g t) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      ∀ x ∈ Icc a b, ‖F n x - F m x‖ < ε) ∧
    ∃ f : Icc a b → ℂ, Uniform.complexUniformConvergesValue
      (fun n (x : Icc a b) => F n x) f

end Specs.SingleVariableAnalysis.Ch12.DerivativeUniformCauchy
