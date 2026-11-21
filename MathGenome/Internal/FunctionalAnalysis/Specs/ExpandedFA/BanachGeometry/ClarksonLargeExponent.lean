import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open MeasureTheory
open scoped ENNReal
universe u

namespace ExpandedFA.BanachGeometry.ClarksonLargeExponentSpec

/-- The large-exponent stage of paper.tex, fa2:p2:clarkson (8975–9029).
The proof does not need the source's duality hypothesis, so arbitrary positive
measures are allowed. The scalar field ranges over both ℝ and ℂ. -/
def ClarksonLargeExponent : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
    2 ≤ p.toReal → p ≠ ∞ →
    ∀ f g : Lp 𝕜 p μ,
      let q := p.toReal / (p.toReal - 1)
      (‖f + g‖ ^ p.toReal + ‖f - g‖ ^ p.toReal ≤
        2 * (‖f‖ ^ q + ‖g‖ ^ q) ^ (p.toReal / q)) ∧
      (2 * (‖f‖ ^ q + ‖g‖ ^ q) ^ (p.toReal / q) ≤
        (2 : ℝ) ^ (p.toReal - 1) * (‖f‖ ^ p.toReal + ‖g‖ ^ p.toReal))

end ExpandedFA.BanachGeometry.ClarksonLargeExponentSpec
