import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Independent specification of paper.tex §6.8, p207:W37.
The intersection below is the literal infimum of the sigma-algebras.
The input is only required to be integrable in the ambient probability space. -/

open MeasureTheory Filter
open scoped MeasureTheory Topology

universe u
namespace P207.LevyDownwardSpec

def levy_downward : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : ℕ → MeasurableSpace Ω), Antitone G → (∀ n, G n ≤ m) →
    ∀ (Y : Ω → ℝ), Integrable Y μ →
      Measurable[⨅ n, G n] (μ[Y | ⨅ n, G n]) ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n => μ[Y | G n] ω) atTop
        (𝓝 (μ[Y | ⨅ n, G n] ω))) ∧
      Tendsto (fun n => ∫ ω, ‖μ[Y | G n] ω - μ[Y | ⨅ n, G n] ω‖ ∂μ)
        atTop (𝓝 0)

end P207.LevyDownwardSpec
