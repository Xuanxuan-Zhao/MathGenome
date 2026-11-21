import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.ProcessInterfaces
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Independent statements for paper.tex §6.4, p207:W33.
The supremum being finite is expressed as a uniform real upper bound.
The terminal variable is real-valued everywhere and measurable for the actual
terminal sigma-algebra, without completing it. -/

open MeasureTheory Filter
open scoped MeasureTheory Topology

universe u
namespace P207.SubmartingaleAEConvergenceSpec

def ae_convergence : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ),
    IsSubmartingale X ℱ μ →
    (∃ C : ℝ, ∀ n, (∫ ω, |X n ω| ∂μ) ≤ C) →
    ∃ Xlim : Ω → ℝ, Measurable[terminalSigma ℱ] Xlim ∧ Integrable Xlim μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Xlim ω))

def moment_bound_iff : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ),
    IsSubmartingale X ℱ μ →
    ((∃ C : ℝ, ∀ n, (∫ ω, |X n ω| ∂μ) ≤ C) ↔
      ∃ C : ℝ, ∀ n, (∫ ω, (X n ω)⁺ ∂μ) ≤ C)

end P207.SubmartingaleAEConvergenceSpec
