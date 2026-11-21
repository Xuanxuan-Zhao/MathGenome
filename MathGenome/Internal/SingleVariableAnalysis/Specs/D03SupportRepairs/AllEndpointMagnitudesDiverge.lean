import MathGenome.Internal.SingleVariableAnalysis.Specs.D03SupportRepairs.EndpointMagnitudes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Independent specification of the complete endpoint theorem in paper.tex:85–100
(original manuscript:1739–1742). Both limits use the actual interior filters. -/
namespace Specs.D03SupportRepairs

/-- All eight derivative and actual endpoint secant magnitude limits. -/
def allEndpointMagnitudesDivergeType : Prop :=
  ∀ (F : ℝ → ℝ), (F = Real.arcsin ∨ F = Real.arccos) →
    ∀ (a : ℝ), (a = -1 ∨ a = 1) →
      Filter.Tendsto (derivativeMagnitudeValue F)
        (nhdsWithin a (Set.Ioo (-1 : ℝ) 1)) Filter.atTop ∧
      Filter.Tendsto (fun x : ℝ => secantMagnitudeValue F a x)
        (nhdsWithin a (Set.Ioo (-1 : ℝ) 1)) Filter.atTop

end Specs.D03SupportRepairs
