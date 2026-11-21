import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.EulerBetaApproximation

/-! The shifted limit and the local and endpoint estimates in the first
paragraph of K03.18.beta_gamma (paper.tex:4170–4193). All parameters are real;
only the sequence index is natural. The kernel is extended by zero outside
(0,n], as in the manuscript's three-interval argument. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch18.ShiftedBetaLimit
open Set Filter MeasureTheory
open scoped Topology

abbrev shiftedKernelType := ℝ → ℝ → ℕ → ℝ → ℝ
def shiftedKernelValue : shiftedKernelType := fun p q n =>
  (Ioc (0 : ℝ) (n : ℝ)).indicator
    (fun u => u ^ (q-1) * (1-u/n) ^ ((n : ℝ)+p-1))

def logarithmicEstimate : Prop := ∀ (p R : ℝ) (n : ℕ),
  0 < R → 0 < n → 2*R ≤ (n : ℝ) → ∀ u ∈ Icc (0 : ℝ) R,
  |((n : ℝ)+p-1) * Real.log (1-u/n) + u| ≤
    (2*R^2 + 2*|p-1| *R) / n

def compactUniform : Prop := ∀ (p q η R : ℝ),
  0 < p → 0 < q → 0 < η → η ≤ R →
  TendstoUniformlyOn (shiftedKernelValue p q)
    (GammaDefinition.gammaKernelValue q) atTop (Icc η R)

def domination : Prop := ∀ (p q : ℝ), 0 < p →
  ∀ (n : ℕ), 2 ≤ n → ∀ u > (0 : ℝ),
  0 ≤ shiftedKernelValue p q n u ∧
  shiftedKernelValue p q n u ≤ u^(q-1) * Real.exp (-u/2) ∧
  shiftedKernelValue p q n u ≤ u^(q-1)

def majorantIntegrability : Prop := ∀ q : ℝ, 0 < q →
  IntegrableOn (fun u : ℝ => u^(q-1) * Real.exp (-u/2)) (Ioi 0)

def integrability : Prop := ∀ p q : ℝ, 0 < p → 0 < q →
  ∀ n : ℕ, 2 ≤ n → IntegrableOn (shiftedKernelValue p q n) (Ioi 0)

def properTruncations : Prop := ∀ p q : ℝ, 0 < p →
  ∀ n : ℕ, 2 ≤ n → ∀ a b : ℝ, 0 < a → a ≤ b →
  ∃ h : Ch08.Integral.realIntegrableValue (shiftedKernelValue p q n) a b,
    Ch08.Integral.realIntegralValue _ h = ∫ u in a..b, shiftedKernelValue p q n u

def nearZeroBound : Prop := ∀ p q : ℝ, 0 < p → 0 < q →
  ∀ η > (0 : ℝ), ∀ n : ℕ, 2 ≤ n →
  0 ≤ (∫ u in (0 : ℝ)..η, shiftedKernelValue p q n u) ∧
  (∫ u in (0 : ℝ)..η, shiftedKernelValue p q n u) ≤ η^q/q

def tailBound : Prop := ∀ p q : ℝ, 0 < p → 0 < q →
  ∀ R > (0 : ℝ), ∀ n : ℕ, 2 ≤ n →
  0 ≤ (∫ u in Ioi R, shiftedKernelValue p q n u) ∧
  (∫ u in Ioi R, shiftedKernelValue p q n u) ≤
    ∫ u in Ioi R, u^(q-1) * Real.exp (-u/2)

def uniformSmallTails : Prop := ∀ p q : ℝ, 0 < p → 0 < q →
  ∀ ε > (0 : ℝ), ∃ R > (0 : ℝ), ∀ n : ℕ, 2 ≤ n →
    (∫ u in Ioi R, shiftedKernelValue p q n u) < ε

def scaledIntegral : Prop := ∀ p q : ℝ, 0 < p → 0 < q →
  ∀ n : ℕ, 0 < n →
  (n : ℝ)^q * BetaDefinition.betaValue (p+n) q =
    ∫ u in Ioi (0 : ℝ), shiftedKernelValue p q n u

def independentImproper : Prop := ∀ p q : ℝ, 0 < p → 0 < q →
  ∀ n : ℕ, 2 ≤ n →
  Ch10.SeveralEndpoints.hasIntegralValue .real (shiftedKernelValue p q n)
    (0 : WithBot ℝ) ⊤ ((n : ℝ)^q * BetaDefinition.betaValue (p+n) q)

def kernelIntegralLimit : Prop := ∀ p q : ℝ, 0 < p → ∀ hq : 0 < q,
  Tendsto (fun n : ℕ => ∫ u in Ioi (0 : ℝ), shiftedKernelValue p q n u)
    atTop (𝓝 (GammaDefinition.gammaIntegralValue q hq))

def shiftedBetaLimit : Prop := ∀ p q : ℝ, 0 < p → ∀ hq : 0 < q,
  Tendsto (fun n : ℕ => (n : ℝ)^q * BetaDefinition.betaValue (p+n) q)
    atTop (𝓝 (GammaDefinition.gammaIntegralValue q hq))

end Specs.SingleVariableAnalysis.Ch18.ShiftedBetaLimit
