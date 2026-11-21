import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.ConvergenceDefinitions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict

/-!
Independent statements for paper.tex:2244–2269.

The first assertion uses the original measurable space and a measurable null
exception, with no completeness assumption. `RCLike` includes both real and
complex scalar functions. The conclusion is the upstream literal uniform
convergence predicate, with a strict bound on the exceptional measure.

For the real-line assertion the native Borel Lebesgue measure is completed:
`NullMeasurableSpace ℝ volume` has precisely the Lebesgue measurable sets and
`volume.completion` has the same outer values as `volume`. Functions are on
the subtype E₀, with the trace of this completed sigma-algebra; they need not
extend measurably for the Borel sigma-algebra. Closedness refers to the usual
topology of ℝ, not relative closedness in E₀. The induced measure on E₀ is
the pullback under its measurable inclusion.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

universe u
noncomputable section

namespace Specs.D11.Ch07.Egorov

open Specs.D11.Ch07.ConvergenceDefinitions

def egorov : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (f : ℕ → X → 𝕜) (g : X → 𝕜),
    μ univ < ∞ → (∀ n, Measurable (f n)) → Measurable g →
    aeConverges_value μ f g → almostUniformConverges_value μ f g

def egorov_closed : Prop :=
  let μB : Measure ℝ := volume
  letI : MeasurableSpace ℝ :=
    inferInstanceAs (MeasurableSpace (NullMeasurableSpace ℝ μB))
  let μ : Measure ℝ := μB.completion
  ∀ {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (E₀ : Set ℝ), MeasurableSet E₀ → μ E₀ < ∞ →
    ∀ (f : ℕ → E₀ → 𝕜) (g : E₀ → 𝕜),
      (∀ n, Measurable (f n)) → Measurable g →
      aeConverges_value (μ.comap (Subtype.val : E₀ → ℝ)) f g →
      ∀ ε : ℝ, 0 < ε → ∃ F : Set ℝ,
        IsClosed F ∧ F ⊆ E₀ ∧ μ (E₀ \ F) < ENNReal.ofReal ε ∧
        uniformConvergesOn_value f g {x : E₀ | (x : ℝ) ∈ F}

end Specs.D11.Ch07.Egorov
