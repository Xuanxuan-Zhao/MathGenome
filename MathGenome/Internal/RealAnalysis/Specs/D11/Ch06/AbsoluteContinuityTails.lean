import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral

/-! Independent statements for paper.tex:1878–1888.
Both estimates concern one measurable, absolutely integrable scalar function
on an arbitrary positive measure space. RCLike includes real and complex
scalars. The set integrals use the shared nonnegative integral of the
indicator times the absolute value, as in the source's restriction convention.
The tolerances and the small-set threshold are finite real numbers.
-/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace Specs.D11.Ch06.AbsoluteContinuityTails

open Specs.D11.Ch05.NonnegativeIntegral
open Specs.D11.Ch06.ScalarIntegral

def small_sets : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜),
    scalarIntegrable_value μ f → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ E : Set X, MeasurableSet E →
        μ E < ENNReal.ofReal δ →
        nonnegativeIntegral_value μ (E.indicator (fun x => ENNReal.ofReal ‖f x‖)) <
          ENNReal.ofReal ε

def finite_measure_tail : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜),
    scalarIntegrable_value μ f → ∀ ε : ℝ, 0 < ε →
      ∃ A : Set X, MeasurableSet A ∧ μ A < ∞ ∧
        nonnegativeIntegral_value μ (Aᶜ.indicator (fun x => ENNReal.ofReal ‖f x‖)) <
          ENNReal.ofReal ε

end Specs.D11.Ch06.AbsoluteContinuityTails
