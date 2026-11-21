import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.CharacterValueIntegrality
import MathGenome.Internal.AlgebraCore.P103.Ch08.CharacterConstructions
import Mathlib.RepresentationTheory.Character

namespace P103.Ch08

/-- Every ordinary character value of a finite group is an algebraic integer.
No irreducibility or nonzero assumption is required. -/
theorem character_integral : CharacterValueIntegralitySpecs.character_integralType := by
  intro G V _ _ _ _ _ ρ g
  exact Representation.isIntegral_character ρ g

end P103.Ch08
