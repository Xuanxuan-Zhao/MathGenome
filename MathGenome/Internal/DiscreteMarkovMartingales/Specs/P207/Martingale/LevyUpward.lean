import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.ProcessInterfaces
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! Independent statements for paper.tex §6.7 (W36).
The terminal sigma algebra is the supremum of the increasing filtration.
The input is only ambient integrable (or in Lp); it need not be measurable
with respect to the terminal sigma algebra. -/

open MeasureTheory Filter
open scoped MeasureTheory Topology

universe u
namespace P207.LevyUpwardSpec

def levy_upward : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (Y : Ω → ℝ), Integrable Y μ →
    (∀ᵐ ω ∂μ, Tendsto (fun n => μ[Y | ℱ n] ω) atTop
      (𝓝 (μ[Y | terminalSigma ℱ] ω))) ∧
    Tendsto (fun n => ∫ ω, ‖μ[Y | ℱ n] ω - μ[Y | terminalSigma ℱ] ω‖ ∂μ)
      atTop (𝓝 0)

def levy_upward_lp : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (Y : Ω → ℝ) (p : ℝ), 1 < p →
    MemLp Y (ENNReal.ofReal p) μ →
    MemLp (μ[Y | terminalSigma ℱ]) (ENNReal.ofReal p) μ ∧
    Tendsto (fun n => eLpNorm (μ[Y | ℱ n] - μ[Y | terminalSigma ℱ])
      (ENNReal.ofReal p) μ) atTop (𝓝 0)

end P207.LevyUpwardSpec
