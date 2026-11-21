import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.ProcessInterfaces
import Mathlib.Probability.Process.LimitProcess
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! The infinite-series conclusions of paper.tex §6.9, p207:W38.
Square integrability is explicit at every time. Series finiteness means
`Summable`, and every real `tsum` in the conclusions has this hypothesis.
The terminal variable is the canonical `limitProcess`, as in W35. -/

open MeasureTheory Filter
open scoped MeasureTheory Topology

universe u
namespace P207.L2SummabilityConvergenceSpec

def l2_bounded_iff_summable : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ),
    IsMartingale M ℱ μ → (∀ n, MemLp (M n) 2 μ) →
    ((∃ C : ℝ, ∀ n, (∫ ω, M n ω ^ 2 ∂μ) ≤ C) ↔
      Summable (fun k => ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ))

def convergence_and_energy : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ),
    IsMartingale M ℱ μ → (∀ n, MemLp (M n) 2 μ) →
    Summable (fun k => ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ) →
      Measurable[terminalSigma ℱ] (ℱ.limitProcess M μ) ∧
      MemLp (ℱ.limitProcess M μ) 2 μ ∧
      Integrable (ℱ.limitProcess M μ) μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n => M n ω) atTop (𝓝 (ℱ.limitProcess M μ ω))) ∧
      Tendsto (fun n => eLpNorm (M n - ℱ.limitProcess M μ) 2 μ) atTop (𝓝 0) ∧
      (∀ n, M n =ᵐ[μ] μ[ℱ.limitProcess M μ | ℱ n]) ∧
      (∫ ω, ℱ.limitProcess M μ ω ^ 2 ∂μ) = (∫ ω, M 0 ω ^ 2 ∂μ) +
        ∑' k, ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ ∧
      ∀ n, Summable (fun k => ∫ ω, (M (n + k + 1) ω - M (n + k) ω) ^ 2 ∂μ) ∧
        (∫ ω, (ℱ.limitProcess M μ ω - M n ω) ^ 2 ∂μ) =
          ∑' k, ∫ ω, (M (n + k + 1) ω - M (n + k) ω) ^ 2 ∂μ

end P207.L2SummabilityConvergenceSpec
