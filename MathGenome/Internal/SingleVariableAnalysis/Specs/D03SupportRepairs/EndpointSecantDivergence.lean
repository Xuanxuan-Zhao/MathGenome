import MathGenome.Internal.SingleVariableAnalysis.Specs.D03SupportRepairs.EndpointMagnitudes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Independent specification of the secant half of paper.tex:77–90,92–99
(original manuscript:1739–1742). The numerator uses the actual endpoint value. -/
namespace Specs.D03SupportRepairs

/-- All four actual endpoint secant magnitudes diverge through the interior. -/
def endpointSecantDivergenceType : Prop :=
  ∀ (F : ℝ → ℝ), (F = Real.arcsin ∨ F = Real.arccos) →
    ∀ (a : ℝ), (a = -1 ∨ a = 1) →
      Filter.Tendsto (fun x : ℝ => secantMagnitudeValue F a x)
        (nhdsWithin a (Set.Ioo (-1 : ℝ) 1)) Filter.atTop

end Specs.D03SupportRepairs
