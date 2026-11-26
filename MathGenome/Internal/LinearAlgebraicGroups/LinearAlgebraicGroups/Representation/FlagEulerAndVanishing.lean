import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagEulerAndVanishing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagEulerCharacteristic
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.KempfVanishing

universe u

namespace LinearAlgebraicGroups.Representation.FlagEulerAndVanishing

/-- The equivariant Euler characteristic formula and Kempf vanishing for
the character line bundles on the opposite-Borel flag. -/
theorem flagEulerAndVanishing : Specs.FlagEulerAndVanishing.Statement.{u} :=
  ⟨FlagEulerCharacteristic.flagEulerCharacteristic, KempfVanishing.kempfVanishing⟩

end LinearAlgebraicGroups.Representation.FlagEulerAndVanishing
