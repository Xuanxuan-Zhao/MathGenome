import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.ProcessInterfaces
import Mathlib.Probability.Process.LimitProcess
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Independent statements for paper.tex §6.6 (W35). The moment hypothesis
includes integrability of every real power, so a default Bochner integral
cannot supply a spurious finite bound. The terminal variable is the same
`limitProcess` representative as in terminal closure. -/
open MeasureTheory Filter
open scoped MeasureTheory Topology
universe u
namespace P207.LpConvergenceSpec

def lp_martingale_convergence : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ), IsMartingale M ℱ μ →
    ∀ (p : ℝ), 1 < p →
    (∀ n, Integrable (fun ω => |M n ω| ^ p) μ) →
    ∀ (C : ℝ), (∀ n, (∫ ω, |M n ω| ^ p ∂μ) ≤ C) →
      Measurable[terminalSigma ℱ] (ℱ.limitProcess M μ) ∧
      MemLp (ℱ.limitProcess M μ) (ENNReal.ofReal p) μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n => M n ω) atTop (𝓝 (ℱ.limitProcess M μ ω))) ∧
      Tendsto (fun n => eLpNorm (M n - ℱ.limitProcess M μ) (ENNReal.ofReal p) μ)
        atTop (𝓝 0) ∧
      ∀ n, M n =ᵐ[μ] μ[ℱ.limitProcess M μ | ℱ n]

def exists_lp_martingale_terminal : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ), IsMartingale M ℱ μ →
    ∀ (p : ℝ), 1 < p →
    (∀ n, Integrable (fun ω => |M n ω| ^ p) μ) →
    ∀ (C : ℝ), (∀ n, (∫ ω, |M n ω| ^ p ∂μ) ≤ C) →
      ∃ Y : Ω → ℝ, Y =ᵐ[μ] ℱ.limitProcess M μ ∧
        Measurable[terminalSigma ℱ] Y ∧ MemLp Y (ENNReal.ofReal p) μ ∧
        (∀ᵐ ω ∂μ, Tendsto (fun n => M n ω) atTop (𝓝 (Y ω))) ∧
        Tendsto (fun n => eLpNorm (M n - Y) (ENNReal.ofReal p) μ) atTop (𝓝 0) ∧
        ∀ n, M n =ᵐ[μ] μ[Y | ℱ n]

end P207.LpConvergenceSpec
