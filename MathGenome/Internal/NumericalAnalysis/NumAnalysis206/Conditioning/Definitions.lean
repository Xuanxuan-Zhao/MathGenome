import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Conditioning.Definitions

/-! Absolute and relative condition numbers (paper.tex, W09).

The map is a total extension of the problem on the open domain `U`.
The differentiability argument excludes nondifferentiable or undefined
singular solution maps. Absolute conditioning permits zero input/output;
relative conditioning requires the two nonzero scales explicitly.
-/

universe u v w

namespace NumAnalysis206.Conditioning

/-- Absolute conditioning, defined also at zero input or zero output. -/
noncomputable def absoluteConditionNumber :
    Specs.NumAnalysis206.Conditioning.AbsoluteConditionNumberType.{u, v, w} :=
  fun 𝕜 _ _ _ _ _ _ _ _ _ _ f x _ _ => ‖fderiv 𝕜 f x‖

/-- Relative conditioning with nonzero input and output scales. -/
noncomputable def relativeConditionNumber :
    Specs.NumAnalysis206.Conditioning.RelativeConditionNumberType.{u, v, w} :=
  fun 𝕜 _ _ _ _ _ _ _ _ _ _ f x _ _ _ _ => ‖fderiv 𝕜 f x‖ * ‖x‖ / ‖f x‖

end NumAnalysis206.Conditioning
