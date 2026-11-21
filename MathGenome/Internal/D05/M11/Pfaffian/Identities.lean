import MathGenome.Internal.Specs.D05.M11.Pfaffian.Identities
import MathGenome.Internal.D05.M11.Pfaffian.Congruence
import MathGenome.Internal.D05.M11.Pfaffian.Square

/-! Assemble the two Pfaffian identities with the shared normalization. -/

namespace D05.M11.Pfaffian.Identities

theorem identities : Specs.D05.M11.Pfaffian.Identities.identities := by
  intro m A P hA
  exact ⟨D05.M11.Pfaffian.Congruence.congruence m A P hA,
    D05.M11.Pfaffian.Square.square m A hA⟩

end D05.M11.Pfaffian.Identities
