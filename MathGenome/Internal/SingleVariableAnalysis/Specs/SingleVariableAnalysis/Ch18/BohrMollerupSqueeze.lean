import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.Convexity
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.GammaEulerLimit

/-! The finite squeeze and the two limits in K03.18.bohr_mollerup,
paper.tex:4142–4169. A total real function represents a function on (0,∞):
all hypotheses and conclusions about it are restricted to positive inputs.
The Gamma value is the shared independently convergent improper integral.
The arbitrary initial terms of the two sequences do not affect their limits.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch18.BohrMollerupSqueeze
open Filter
open scoped Topology BigOperators

def admissible (F : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, 0 < x → 0 < F x) ∧ F 1 = 1 ∧
  (∀ x : ℝ, 0 < x → F (x + 1) = x * F x) ∧
  Ch05.Convexity.convexFunctionOnValue (Set.Ioi 0) (fun x => Real.log (F x))

def lower (x : ℝ) (n : ℕ) : ℝ :=
  ((n - 1).factorial : ℝ) * ((n : ℝ) - 1) ^ x /
    ∏ j ∈ Finset.range n, (x + (j : ℝ))

def upper (x : ℝ) (n : ℕ) : ℝ :=
  ((n - 1).factorial : ℝ) * (n : ℝ) ^ x /
    ∏ j ∈ Finset.range n, (x + (j : ℝ))

def factorialValues : Prop := ∀ F : ℝ → ℝ, admissible F →
  ∀ n : ℕ, 1 ≤ n → F (n : ℝ) = ((n - 1).factorial : ℝ)

def squeezeBounds : Prop := ∀ F : ℝ → ℝ, admissible F →
  ∀ x : ℝ, 0 < x → x ≤ 1 → ∀ n : ℕ, 2 ≤ n →
    lower x n ≤ F x ∧ F x ≤ upper x n

def squeezeLimits : Prop := ∀ (x : ℝ) (hx : 0 < x), x ≤ 1 →
  Tendsto (lower x) atTop (𝓝 (GammaDefinition.gammaIntegralValue x hx)) ∧
  Tendsto (upper x) atTop (𝓝 (GammaDefinition.gammaIntegralValue x hx))

end Specs.SingleVariableAnalysis.Ch18.BohrMollerupSqueeze
