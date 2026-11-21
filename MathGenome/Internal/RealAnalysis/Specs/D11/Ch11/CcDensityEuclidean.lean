import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.CcCzero
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! Independent statement for paper.tex:3654–3666, continuous approximation
in Euclidean space. `Point d` is Euclidean ℝ^d, with d ≥ 1. The measurable
space and measure are the full completed Lebesgue objects from Chapter 3.
The native Cc type uses genuinely compact topological support, as identified
in Chapter 19. `Lp` is the ordinary a.e. quotient, with the source-space
identification supplied by the upstream quotient construction. RCLike
includes both real and complex scalars. Finite exponents include p = 1. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Specs.D11.Ch11.CcDensityEuclidean
open _root_.D11.Ch03
open Specs.D11.Ch03.LebesgueMeasures

/-- Every ordinary Lp class is arbitrarily close to the class of a Cc function. -/
def cc_density : Prop :=
  ∀ (d : ℕ) [NeZero d] (𝕜 : Type) [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    letI := lebesgueSpace_value d
    ∀ f : Lp 𝕜 p (lebesgue_value d), ∀ ε : ℝ, 0 < ε →
      ∃ g : CompactlySupportedContinuousMap (Point d) 𝕜,
        ∃ hg : MemLp (g : Point d → 𝕜) p (lebesgue_value d),
          ‖f - hg.toLp g‖ < ε

end Specs.D11.Ch11.CcDensityEuclidean
