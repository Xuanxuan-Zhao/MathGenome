import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.RadixModel

/-! Independent statement of the first assertion of paper.tex, Theorem W04. -/
namespace NumAnalysis206.Rounding.Specs

/-- The absolute nearest-rounding estimate throughout the underflow region,
including its endpoints, for a format with gradual underflow. -/
def gradualUnderflowBound : Prop :=
  ∀ (P : RadixFormat), P.gradual = true → ∀ (x : ℝ),
    |x| ≤ aminValue P → |flValue P x - x| ≤ (P.β : ℝ) ^ P.emin / 2

end NumAnalysis206.Rounding.Specs
