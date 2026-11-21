import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Independent statements for paper.tex:1994–2011.

The shared scalar-integrability predicate includes measurability on the original
sigma-algebra and finite absolute integral. Set integrals below use the native
notation for integration against `μ.restrict E`, the canonical ambient
restriction. They are the shared scalar integral by its defining value;
integrability on every such restriction follows from the ambient integrability
hypothesis. Thus no totalized value on a nonintegrable function is used.

The conclusions use the shared measurable-null-envelope definition of a.e.
No finiteness, sigma-finiteness or completeness hypothesis is imposed.
-/

open MeasureTheory

universe u
noncomputable section

namespace Specs.D11.Ch06.IntegralDetection

open ScalarIntegral
open Specs.D11.Ch04.AeCommonException

/-- Nonnegative integrals on all measurable sets detect nonnegativity a.e. -/
def nonnegative_detection : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ),
    scalarIntegrable_value μ f →
    (∀ E : Set X, MeasurableSet E → 0 ≤ ∫ x in E, f x ∂μ) →
    almostEverywhere_value μ (fun x => 0 ≤ f x)

/-- `RCLike` includes both the real and complex conclusions in the source. -/
def equality_detection : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f g : X → 𝕜),
    scalarIntegrable_value μ f → scalarIntegrable_value μ g →
    (∀ E : Set X, MeasurableSet E →
      (∫ x in E, f x ∂μ) = ∫ x in E, g x ∂μ) →
    aeEq_value μ f g

end Specs.D11.Ch06.IntegralDetection
