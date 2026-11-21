import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.GammaEulerLimit

/-! K03.18.beta_gamma, paper.tex:4170–4210. The Beta and Gamma values
are the shared independently convergent improper integrals. Products have
exactly n factors, including the empty product when n = 0. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch18.BetaGamma
open Filter
open scoped Topology BigOperators

abbrev risingProductType := ℝ → ℕ → ℝ
def risingProductValue : risingProductType := fun p n =>
  ∏ j ∈ Finset.range n, (p + (j : ℝ))

def risingProductPositive : Prop := ∀ p : ℝ, 0 < p → ∀ n : ℕ,
  0 < risingProductValue p n

def betaShiftRecurrence : Prop := ∀ p q : ℝ, 0 < p → 0 < q → ∀ n : ℕ,
  BetaDefinition.betaValue (p + n) q =
    risingProductValue p n * BetaDefinition.betaValue p q / risingProductValue (p+q) n

/-- Positivity on the tail where both normalizations have positive bases,
and positivity of both limiting quotients. -/
def ratioPositive : Prop := ∀ p q : ℝ, ∀ hp : 0 < p, ∀ hq : 0 < q,
  (∀ n : ℕ, 2 ≤ n →
    0 < ((n : ℝ)-1)^q * risingProductValue p n / risingProductValue (p+q) n ∧
    0 < risingProductValue (p+q) n / ((n : ℝ)^q * risingProductValue p n)) ∧
  0 < GammaDefinition.gammaIntegralValue (p+q) (add_pos hp hq) /
    GammaDefinition.gammaIntegralValue p hp ∧
  0 < GammaDefinition.gammaIntegralValue p hp /
    GammaDefinition.gammaIntegralValue (p+q) (add_pos hp hq)

/-- Quotient of the Euler approximants with index n-1. -/
def eulerRatioLimit : Prop := ∀ p q : ℝ, ∀ hp : 0 < p, ∀ hq : 0 < q,
  Tendsto (fun n : ℕ => ((n : ℝ)-1)^q * risingProductValue p n /
    risingProductValue (p+q) n) atTop
    (𝓝 (GammaDefinition.gammaIntegralValue (p+q) (add_pos hp hq) /
      GammaDefinition.gammaIntegralValue p hp))

/-- Inversion and the normalization n/(n-1) give this second ratio. -/
def inverseRatioLimit : Prop := ∀ p q : ℝ, ∀ hp : 0 < p, ∀ hq : 0 < q,
  Tendsto (fun n : ℕ => risingProductValue (p+q) n /
    ((n : ℝ)^q * risingProductValue p n)) atTop
    (𝓝 (GammaDefinition.gammaIntegralValue p hp /
      GammaDefinition.gammaIntegralValue (p+q) (add_pos hp hq)))

def betaGammaIdentity : Prop := ∀ p q : ℝ, ∀ hp : 0 < p, ∀ hq : 0 < q,
  BetaDefinition.betaValue p q =
    GammaDefinition.gammaIntegralValue p hp * GammaDefinition.gammaIntegralValue q hq /
      GammaDefinition.gammaIntegralValue (p+q) (add_pos hp hq)

end Specs.SingleVariableAnalysis.Ch18.BetaGamma
