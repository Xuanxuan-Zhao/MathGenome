import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.ProcessInterfaces
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.UniformIntegrability

/-! Independent statement of the submartingale clause of paper.tex §6.5,
p207:W34. The probability space need not be complete. The terminal variable
is measurable for the actual supremum of the filtration, and convergence in
L¹ means convergence of the expectations of absolute differences. -/

open MeasureTheory Filter
open scoped MeasureTheory Topology

universe u
namespace P207.UISubmartingaleClosureSpec

def terminal_closure : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ),
    IsSubmartingale X ℱ μ →
    Specs.P207.Martingale.UniformIntegrability.SourceUniformIntegrableValue μ X →
    ∃ Xlim : Ω → ℝ, Measurable[terminalSigma ℱ] Xlim ∧ Integrable Xlim μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Xlim ω))) ∧
      Tendsto (fun n => ∫ ω, |X n ω - Xlim ω| ∂μ) atTop (𝓝 0) ∧
      ∀ n, X n ≤ᵐ[μ] μ[Xlim | ℱ n]

end P207.UISubmartingaleClosureSpec
