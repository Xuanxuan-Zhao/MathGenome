import MathGenome.Internal.SingleVariableAnalysis.D03SupportRepairs.EndpointSecantDivergence

/-! The complete endpoint theorem in paper.tex:85–100
(original manuscript:1739–1742), assembled from its two proved stages.
The imported `leftEndpointInteriorNeBot` and `rightEndpointInteriorNeBot`
establish nontriviality of both approach filters without additional assumptions. -/
open Filter Set

namespace D03SupportRepairs

/-- For either canonical inverse branch and either endpoint, both the derivative
magnitude and the actual endpoint secant magnitude tend to positive infinity. -/
theorem allEndpointMagnitudesDiverge
    (F : ℝ → ℝ) (hF : F = Real.arcsin ∨ F = Real.arccos)
    (a : ℝ) (ha : a = -1 ∨ a = 1) :
    Tendsto (derivativeMagnitude F)
      (nhdsWithin a (Ioo (-1 : ℝ) 1)) atTop ∧
    Tendsto (fun x : ℝ => secantMagnitude F a x)
      (nhdsWithin a (Ioo (-1 : ℝ) 1)) atTop :=
  ⟨endpointDerivativeDivergence F hF a ha, endpointSecantDivergence F hF a ha⟩

end D03SupportRepairs
