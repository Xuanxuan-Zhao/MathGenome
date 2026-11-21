import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.BetaDefinition
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.GammaDefinition
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! The scaled approximation in K03.18.gamma_euler_limit, paper.tex:4066–4101.
The integral values refer to the shared Beta/Gamma objects. Proper Darboux
bridges and independent improper convergence are separate obligations below. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch18.EulerBetaApproximation
open Set Filter MeasureTheory
open scoped Topology

abbrev scaledKernelType := ℝ → ℕ → ℝ → ℝ
/-- The extension at zero is immaterial to every integral and positive compact. -/
def scaledKernelValue : scaledKernelType := fun s n =>
  (Ioc (0 : ℝ) (n : ℝ)).indicator (fun u => u ^ (s - 1) * (1 - u / n) ^ n)

def logarithmicEstimate : Prop := ∀ (R : ℝ) (n : ℕ), 0 < R → 0 < n →
  2 * R ≤ (n : ℝ) → ∀ u ∈ Icc (0 : ℝ) R,
  |(n : ℝ) * Real.log (1 - u / n) + u| ≤ 2 * R ^ 2 / n

def compactUniform : Prop := ∀ (s η R : ℝ), 0 < s → 0 < η → η ≤ R →
  TendstoUniformlyOn (scaledKernelValue s) (GammaDefinition.gammaKernelValue s)
    atTop (Icc η R)

def domination : Prop := ∀ (s : ℝ) (n : ℕ) (u : ℝ), 0 < u →
  0 ≤ scaledKernelValue s n u ∧
  scaledKernelValue s n u ≤ GammaDefinition.gammaKernelValue s u ∧
  scaledKernelValue s n u ≤ u ^ (s - 1)

def integrability : Prop := ∀ (s : ℝ), 0 < s → ∀ n : ℕ,
  IntegrableOn (scaledKernelValue s n) (Ioi 0)

def properTruncations : Prop := ∀ (s : ℝ) (n : ℕ), 0 < n →
  ∀ (a b : ℝ), 0 < a → a ≤ b →
  ∃ h : Ch08.Integral.realIntegrableValue (scaledKernelValue s n) a b,
    Ch08.Integral.realIntegralValue _ h = ∫ u in a..b, scaledKernelValue s n u

def scaledIntegral : Prop := ∀ (s : ℝ), 0 < s → ∀ n : ℕ, 0 < n →
  (n : ℝ) ^ s * BetaDefinition.betaValue s ((n : ℝ) + 1) =
    ∫ u in Ioi (0 : ℝ), scaledKernelValue s n u

def independentImproper : Prop := ∀ (s : ℝ), 0 < s → ∀ n : ℕ, 0 < n →
  Ch10.SeveralEndpoints.hasIntegralValue .real (scaledKernelValue s n)
    (0 : WithBot ℝ) ⊤ ((n : ℝ) ^ s * BetaDefinition.betaValue s ((n : ℝ) + 1))

def nearZeroBound : Prop := ∀ (s : ℝ), 0 < s → ∀ (η : ℝ), 0 < η → ∀ n : ℕ,
  0 ≤ (∫ u in (0 : ℝ)..η, scaledKernelValue s n u) ∧
  (∫ u in (0 : ℝ)..η, scaledKernelValue s n u) ≤ η ^ s / s

def tailBound : Prop := ∀ (s : ℝ), 0 < s → ∀ (R : ℝ), 0 < R → ∀ n : ℕ,
  0 ≤ (∫ u in Ioi R, scaledKernelValue s n u) ∧
  (∫ u in Ioi R, scaledKernelValue s n u) ≤
    ∫ u in Ioi R, GammaDefinition.gammaKernelValue s u

def uniformSmallTails : Prop := ∀ (s : ℝ), 0 < s → ∀ ε > (0 : ℝ),
  ∃ R > (0 : ℝ), ∀ n : ℕ, (∫ u in Ioi R, scaledKernelValue s n u) < ε

def betaApproximation : Prop := ∀ (s : ℝ) (hs : 0 < s),
  Tendsto (fun n : ℕ => (n : ℝ) ^ s * BetaDefinition.betaValue s ((n : ℝ) + 1))
    atTop (𝓝 (GammaDefinition.gammaIntegralValue s hs))

end Specs.SingleVariableAnalysis.Ch18.EulerBetaApproximation
