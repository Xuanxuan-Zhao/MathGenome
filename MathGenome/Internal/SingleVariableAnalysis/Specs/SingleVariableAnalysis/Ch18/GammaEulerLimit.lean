import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.BetaRecurrence
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.GammaDefinition

/-! K03.18.gamma_euler_limit, paper.tex:4066–4101.
Both ordinary sequence limits have the value of the previously constructed
improper Gamma integral. The product includes s through s+n. Indexing by ℕ
atTop expresses the positive-integer limit, irrespective of the initial term.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch18.GammaEulerLimit
open Filter
open scoped Topology BigOperators

def gammaEulerLimit : Prop := ∀ (s : ℝ) (hs : 0 < s),
  Tendsto (fun n : ℕ => (n : ℝ) ^ s * BetaDefinition.betaValue s ((n : ℝ) + 1))
    atTop (𝓝 (GammaDefinition.gammaIntegralValue s hs)) ∧
  Tendsto (fun n : ℕ =>
    (n.factorial : ℝ) * (n : ℝ) ^ s /
      ∏ j ∈ Finset.range (n + 1), (s + (j : ℝ)))
    atTop (𝓝 (GammaDefinition.gammaIntegralValue s hs))

end Specs.SingleVariableAnalysis.Ch18.GammaEulerLimit
