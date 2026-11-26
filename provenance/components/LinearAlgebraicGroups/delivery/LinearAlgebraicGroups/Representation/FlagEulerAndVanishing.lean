import Specs.LinearAlgebraicGroups.Representation.FlagEulerAndVanishing
import LinearAlgebraicGroups.Representation.FlagEulerCharacteristic
import LinearAlgebraicGroups.Representation.KempfVanishing

universe u

namespace LinearAlgebraicGroups.Representation.FlagEulerAndVanishing

/-- The equivariant Euler characteristic formula and Kempf vanishing for
the character line bundles on the opposite-Borel flag. -/
theorem flagEulerAndVanishing : Specs.FlagEulerAndVanishing.Statement.{u} :=
  ⟨FlagEulerCharacteristic.flagEulerCharacteristic, KempfVanishing.kempfVanishing⟩

end LinearAlgebraicGroups.Representation.FlagEulerAndVanishing
