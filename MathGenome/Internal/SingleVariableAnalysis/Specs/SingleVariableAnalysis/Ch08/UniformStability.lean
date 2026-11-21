import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Uniform

/-! K03.08.uniform_stability, paper.tex:2125–2142, also K03.12.integration.
The integrals are the existing proper Darboux integrals. Uniform convergence
is required only on the closed interval, represented by its subtype. The
real supremum in the estimate is finite for every index: integrability bounds
each approximant, and the conclusion bounds the limit. No continuity is assumed.
The assertions include the singleton interval and both scalar choices.
-/
namespace Specs.SingleVariableAnalysis.Ch08.UniformStability
open scoped Topology

def realUniformStability : Prop :=
  ∀ (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
    (hF : ∀ n, Integral.realIntegrableValue (F n) a b) →
    Specs.SingleVariableAnalysis.Ch12.Uniform.realUniformConvergesValue
      (fun n (x : Set.Icc a b) => F n x) (fun x => f x) →
    ∃ hf : Integral.realIntegrableValue f a b,
      (∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M) ∧
      (∀ n, ‖Integral.realIntegralValue f hf - Integral.realIntegralValue (F n) (hF n)‖ ≤
        (b - a) * sSup ((fun x => ‖f x - F n x‖) '' Set.Icc a b)) ∧
      Filter.Tendsto
        (fun n => (b - a) * sSup ((fun x => ‖f x - F n x‖) '' Set.Icc a b))
        Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => Integral.realIntegralValue (F n) (hF n))
        Filter.atTop (𝓝 (Integral.realIntegralValue f hf))

def complexUniformStability : Prop :=
  ∀ (F : ℕ → ℝ → ℂ) (f : ℝ → ℂ) {a b : ℝ}, a ≤ b →
    (hF : ∀ n, Integral.complexIntegrableValue (F n) a b) →
    Specs.SingleVariableAnalysis.Ch12.Uniform.complexUniformConvergesValue
      (fun n (x : Set.Icc a b) => F n x) (fun x => f x) →
    ∃ hf : Integral.complexIntegrableValue f a b,
      (∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M) ∧
      (∀ n, ‖Integral.complexIntegralValue f hf - Integral.complexIntegralValue (F n) (hF n)‖ ≤
        (b - a) * sSup ((fun x => ‖f x - F n x‖) '' Set.Icc a b)) ∧
      Filter.Tendsto
        (fun n => (b - a) * sSup ((fun x => ‖f x - F n x‖) '' Set.Icc a b))
        Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => Integral.complexIntegralValue (F n) (hF n))
        Filter.atTop (𝓝 (Integral.complexIntegralValue f hf))

end Specs.SingleVariableAnalysis.Ch08.UniformStability
