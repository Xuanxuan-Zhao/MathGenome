import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.GammaDefinition

/-! Independent statements for K03.18.gamma_recurrence, paper.tex:4048–4065.
`gammaIntegralValue` is the upstream sum of the two independent proper
Riemann limits. Its positive-parameter domain is retained throughout.
The boundary terms in integration by parts have independent limits.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch18.GammaRecurrence
open Filter
open scoped Topology

/-- The lower boundary term, approached from within the positive half-line. -/
def boundaryAtZero : Prop := ∀ (s : ℝ), 0 < s →
  Tendsto (fun t : ℝ => -(t ^ s * Real.exp (-t))) (𝓝[>] 0) (𝓝 0)

/-- The upper boundary term; no coupling with the lower cutoff is imposed. -/
def boundaryAtInfinity : Prop := ∀ (s : ℝ), 0 < s →
  Tendsto (fun t : ℝ => -(t ^ s * Real.exp (-t))) atTop (𝓝 0)

def recurrence : Prop := ∀ (s : ℝ) (hs : 0 < s),
  GammaDefinition.gammaIntegralValue (s + 1) (add_pos hs zero_lt_one) =
    s * GammaDefinition.gammaIntegralValue s hs

def atOne : Prop := GammaDefinition.gammaIntegralValue 1 zero_lt_one = 1

/-- Natural numbers enumerate exactly the nonnegative integers, including zero. -/
def factorialValues : Prop := ∀ n : ℕ,
  GammaDefinition.gammaIntegralValue ((n : ℝ) + 1)
    (lt_add_of_le_of_pos (Nat.cast_nonneg n) zero_lt_one) = (n.factorial : ℝ)

end Specs.SingleVariableAnalysis.Ch18.GammaRecurrence
