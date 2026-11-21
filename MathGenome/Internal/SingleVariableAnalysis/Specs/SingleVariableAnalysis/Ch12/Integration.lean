import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Uniform

/-! K03.12.integration, paper.tex:1246–1261; K03.08.uniform_stability,
paper.tex:2125–2142.
The integrals are the existing proper Darboux integrals. Uniform convergence
is required only on the closed interval, represented by its subtype. The
real supremum in the estimate is finite for every index: integrability bounds
each approximant, and the conclusion bounds the limit. No continuity is assumed.
The assertions include the singleton interval and both scalar choices.
-/
namespace Specs.SingleVariableAnalysis.Ch12.Integration
open scoped Topology

def realUniformIntegration : Prop :=
  ∀ (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
    (hF : ∀ n, Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue (F n) a b) →
    Specs.SingleVariableAnalysis.Ch12.Uniform.realUniformConvergesValue
      (fun n (x : Set.Icc a b) => F n x) (fun x => f x) →
    ∃ hf : Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue f a b,
      (∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M) ∧
      (∀ n, ‖Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue f hf - Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue (F n) (hF n)‖ ≤
        (b - a) * sSup ((fun x => ‖f x - F n x‖) '' Set.Icc a b)) ∧
      Filter.Tendsto
        (fun n => (b - a) * sSup ((fun x => ‖f x - F n x‖) '' Set.Icc a b))
        Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue (F n) (hF n))
        Filter.atTop (𝓝 (Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue f hf))

def complexUniformIntegration : Prop :=
  ∀ (F : ℕ → ℝ → ℂ) (f : ℝ → ℂ) {a b : ℝ}, a ≤ b →
    (hF : ∀ n, Specs.SingleVariableAnalysis.Ch08.Integral.complexIntegrableValue (F n) a b) →
    Specs.SingleVariableAnalysis.Ch12.Uniform.complexUniformConvergesValue
      (fun n (x : Set.Icc a b) => F n x) (fun x => f x) →
    ∃ hf : Specs.SingleVariableAnalysis.Ch08.Integral.complexIntegrableValue f a b,
      (∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M) ∧
      (∀ n, ‖Specs.SingleVariableAnalysis.Ch08.Integral.complexIntegralValue f hf - Specs.SingleVariableAnalysis.Ch08.Integral.complexIntegralValue (F n) (hF n)‖ ≤
        (b - a) * sSup ((fun x => ‖f x - F n x‖) '' Set.Icc a b)) ∧
      Filter.Tendsto
        (fun n => (b - a) * sSup ((fun x => ‖f x - F n x‖) '' Set.Icc a b))
        Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => Specs.SingleVariableAnalysis.Ch08.Integral.complexIntegralValue (F n) (hF n))
        Filter.atTop (𝓝 (Specs.SingleVariableAnalysis.Ch08.Integral.complexIntegralValue f hf))

/-- The source's zero-length case, without regularity assumptions. -/
def realDegenerateIntegration : Prop :=
  ∀ (f : ℝ → ℝ) (a : ℝ),
    Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue f a a ∧
    ∀ hf : Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue f a a, Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue f hf = 0

/-- The same zero-length convention for complex scalars. -/
def complexDegenerateIntegration : Prop :=
  ∀ (f : ℝ → ℂ) (a : ℝ),
    Specs.SingleVariableAnalysis.Ch08.Integral.complexIntegrableValue f a a ∧
    ∀ hf : Specs.SingleVariableAnalysis.Ch08.Integral.complexIntegrableValue f a a, Specs.SingleVariableAnalysis.Ch08.Integral.complexIntegralValue f hf = 0

end Specs.SingleVariableAnalysis.Ch12.Integration
