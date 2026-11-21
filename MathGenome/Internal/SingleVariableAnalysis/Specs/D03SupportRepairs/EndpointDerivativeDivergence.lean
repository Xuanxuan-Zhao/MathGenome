import MathGenome.Internal.SingleVariableAnalysis.Specs.D03SupportRepairs.EndpointMagnitudes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Independent propositions for the derivative half of the endpoint theorem,
paper.tex:82–89,92–96 (original manuscript:1739–1742). -/
namespace Specs.D03SupportRepairs

/-- All four derivative magnitude limits, with precisely the interior interval filter. -/
def endpointDerivativeDivergenceType : Prop :=
  ∀ (F : ℝ → ℝ), (F = Real.arcsin ∨ F = Real.arccos) →
    ∀ (a : ℝ), (a = -1 ∨ a = 1) →
      Filter.Tendsto (derivativeMagnitudeValue F)
        (nhdsWithin a (Set.Ioo (-1 : ℝ) 1)) Filter.atTop

/-- The interior approach at the left endpoint is nonvacuous. -/
def leftEndpointInteriorNeBotType : Prop :=
  Filter.NeBot (nhdsWithin (-1 : ℝ) (Set.Ioo (-1 : ℝ) 1))

/-- The interior approach at the right endpoint is nonvacuous. -/
def rightEndpointInteriorNeBotType : Prop :=
  Filter.NeBot (nhdsWithin (1 : ℝ) (Set.Ioo (-1 : ℝ) 1))

end Specs.D03SupportRepairs
