import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral

/-! Independent statements of paper.tex:1806–1838. The common scalar
interface includes actual measurability and finite absolute integral.
`RCLike` covers both ℝ and ℂ. No size or completeness assumption is made
on the positive measure space. The absolute integral in the last statement
is the shared nonnegative integral; integrability ensures that its `toReal`
is its finite real value. -/

open MeasureTheory
open scoped ENNReal
universe u
noncomputable section

namespace Specs.D11.Ch06.LinearityOrder

open ScalarIntegral
open Specs.D11.Ch04.AeCommonException
open Specs.D11.Ch05.NonnegativeIntegral

/-- The conclusion supplies integrability before evaluating the new integral. -/
def linearity : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f g : X → 𝕜)
    (a b : 𝕜) (hf : scalarIntegrable_value μ f) (hg : scalarIntegrable_value μ g),
    ∃ hab : scalarIntegrable_value μ (fun x => a * f x + b * g x),
      scalarIntegral_value μ (fun x => a * f x + b * g x) hab =
        a * scalarIntegral_value μ f hf + b * scalarIntegral_value μ g hg

/-- Order holds outside a measurable null envelope in the original space. -/
def monotonicity : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ)
    (hf : scalarIntegrable_value μ f) (hg : scalarIntegrable_value μ g),
    almostEverywhere_value μ (fun x => f x ≤ g x) →
      scalarIntegral_value μ f hf ≤ scalarIntegral_value μ g hg

/-- Norm is real absolute value for ℝ and the complex modulus for ℂ. -/
def absolute_value_bound : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜)
    (hf : scalarIntegrable_value μ f),
    ‖scalarIntegral_value μ f hf‖ ≤
      (nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖f x‖)).toReal

end Specs.D11.Ch06.LinearityOrder
