import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.TestFunctionLFTopology
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Independent statement of paper.tex, `fa2:p4:sobolev-one`.
The scalar field is real or complex. The domain and coordinate vectors are
the accepted Euclidean coordinates; volume is ordinary Lebesgue measure.
The ENNReal inequality records the usual Lp norm, and membership/integrability
explicitly ensure that all norms in the estimate are finite. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace Specs.ExpandedFA.Sobolev.EndpointSobolevInequality
open _root_.ExpandedFA.Distributions

/-- The endpoint exponent is exactly d/(d-1), with one constant for each d,
independent of the function, its support and its scalar field. -/
def EndpointInequality : Prop :=
  ∀ (d : ℕ), 1 < d → ∃ C : ℝ≥0,
    ∀ (𝕜 : Type) [RCLike 𝕜] (u : Domain d → 𝕜),
      ContDiff ℝ 1 u → HasCompactSupport u →
      MemLp u (ENNReal.ofReal ((d : ℝ) / ((d : ℝ) - 1))) volume ∧
      (∀ j : Fin d, Integrable (fun x => fderiv ℝ u x (coordinateVector j)) volume) ∧
      eLpNorm u (ENNReal.ofReal ((d : ℝ) / ((d : ℝ) - 1))) volume ≤
        (C : ℝ≥0∞) * ∑ j : Fin d,
          eLpNorm (fun x => fderiv ℝ u x (coordinateVector j)) 1 volume

end Specs.ExpandedFA.Sobolev.EndpointSobolevInequality
