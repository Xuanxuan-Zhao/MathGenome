import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14UniformConvexity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! Clarkson inequalities, paper.tex:4714–4761. Scalars are real or complex,
and the positive measure is arbitrary, including the zero measure. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v
namespace ExpandedFA.P1.Clarkson.Spec

/-- The first sharp Clarkson inequality, including p = 2. -/
def UpperRange : Prop :=
  ∀ (𝕜 : Type v) [RCLike 𝕜] {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (p : ℝ) (hp : 2 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)] (f g : Lp 𝕜 (ENNReal.ofReal p) μ),
    ‖f + g‖ ^ p + ‖f - g‖ ^ p ≤
      (2 : ℝ) ^ (p - 1) * (‖f‖ ^ p + ‖g‖ ^ p)

/-- The second sharp inequality with q = p/(p-1), including p = 2. -/
def LowerRange : Prop :=
  ∀ (𝕜 : Type v) [RCLike 𝕜] {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (p : ℝ) (hp : 1 < p) (hp₂ : p ≤ 2)
    [Fact (1 ≤ ENNReal.ofReal p)] (f g : Lp 𝕜 (ENNReal.ofReal p) μ),
    let q := p / (p - 1)
    ‖f + g‖ ^ q + ‖f - g‖ ^ q ≤
      2 * (‖f‖ ^ p + ‖g‖ ^ p) ^ (q / p)

/-- Uniform convexity in the manuscript's closed-unit-ball formulation.
No sigma-finiteness, finiteness, or nontriviality is assumed. -/
def UniformConvexity : Prop :=
  ∀ (𝕜 : Type v) [RCLike 𝕜] {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (p : ℝ) (hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)],
    C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 (Lp 𝕜 (ENNReal.ofReal p) μ)

end ExpandedFA.P1.Clarkson.Spec
