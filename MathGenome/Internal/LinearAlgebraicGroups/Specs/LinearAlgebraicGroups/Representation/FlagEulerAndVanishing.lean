import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagEulerCharacteristic
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.KempfVanishing

universe u

namespace LinearAlgebraicGroups.Specs.FlagEulerAndVanishing

/-- E10 for a split connected reductive group over any field. The Weyl alternant
formula holds for every character of the split maximal torus. For dominant
characters, the positive cohomology of the same associated line on the
negative-Borel flag vanishes. Both statements use `FlagCohomology.flagCohomology`. -/
def Statement : Prop :=
  FlagEulerCharacteristic.Statement.{u} ∧ KempfVanishing.Statement.{u}

end LinearAlgebraicGroups.Specs.FlagEulerAndVanishing
