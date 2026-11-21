import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.CantorExactMass
import MathGenome.Internal.RealAnalysis.D11.Ch22.CantorDimension

/-!
The upstream construction intervals give the upper bound one. Its lower
bound uses the sharp constant-one Hölder surjection onto [0,1] and the
outer-measure image estimate on arbitrary subsets. Thus it does not impose
measurability on arbitrary covering sets or on their Cantor-map images.
-/

namespace D11.Ch22.CantorExactMass

/-- The exact critical mass, in the coefficient-one diameter normalization. -/
theorem exact_mass : Specs.D11.Ch22.CantorExactMass.exact_mass := by
  exact le_antisymm CantorDimension.mass_upper CantorDimension.mass_lower

end D11.Ch22.CantorExactMass
