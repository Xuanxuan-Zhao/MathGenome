import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachGeometry.ClarksonLargeExponent
import Mathlib.Analysis.Convex.Uniform

/-! The exact Clarkson inequalities and their stated modulus, paper.tex
`fa2:p2:clarkson` (8981–9043). We allow arbitrary positive measures, which
includes every measure satisfying the source's duality hypothesis. The spaces
are the ordinary a.e. quotients, with their usual norms; scalars are ℝ or ℂ.
The modulus estimate includes ε=0 and ε=2 and the zero space. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
universe u

namespace ExpandedFA.BanachGeometry.ClarksonSpec

/-- The explicit valid modulus in the manuscript, with q=p/(p-1). -/
def modulus (p ε : ℝ) : ℝ :=
  let r := max p (p / (p - 1))
  1 - (1 - (ε / 2) ^ r) ^ (1 / r)

abbrev LargeExponent : Prop :=
  ClarksonLargeExponentSpec.ClarksonLargeExponent.{u}

/-- The full q-power inequality in the small-exponent range. -/
def SmallExponent : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
    1 < p.toReal → p.toReal ≤ 2 → p ≠ ∞ →
    ∀ f g : Lp 𝕜 p μ,
      let q := p.toReal / (p.toReal - 1)
      ‖f + g‖ ^ q + ‖f - g‖ ^ q ≤
        2 * (‖f‖ ^ p.toReal + ‖g‖ ^ p.toReal) ^ (q / p.toReal)

/-- The unit-ball estimate with exponent max(p,q), from which the stated
modulus follows. Midpoints are real scalar multiplication by 1/2. -/
def MidpointPower : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
    1 < p.toReal → p ≠ ∞ → ∀ f g : Lp 𝕜 p μ,
    ‖f‖ ≤ 1 → ‖g‖ ≤ 1 →
      let r := max p.toReal (p.toReal / (p.toReal - 1))
      ‖(1 / 2 : ℝ) • (f + g)‖ ^ r +
        ‖(1 / 2 : ℝ) • (f - g)‖ ^ r ≤ 1

/-- Validity of the explicit modulus on the entire closed interval [0,2]. -/
def ModulusEstimate : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
    1 < p.toReal → p ≠ ∞ → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 2 →
      0 ≤ modulus p.toReal ε ∧ (0 < ε → 0 < modulus p.toReal ε) ∧
      ∀ f g : Lp 𝕜 p μ, ‖f‖ ≤ 1 → ‖g‖ ≤ 1 → ε ≤ ‖f - g‖ →
        ‖(1 / 2 : ℝ) • (f + g)‖ ≤ 1 - modulus p.toReal ε

/-- Uniform convexity of the native Lp norm, including the zero space. -/
def UniformConvexity : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
    1 < p.toReal → p ≠ ∞ → UniformConvexSpace (Lp 𝕜 p μ)

end ExpandedFA.BanachGeometry.ClarksonSpec
