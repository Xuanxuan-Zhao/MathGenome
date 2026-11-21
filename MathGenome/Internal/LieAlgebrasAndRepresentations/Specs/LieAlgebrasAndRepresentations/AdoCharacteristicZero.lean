import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Specs.LieAlgebrasAndRepresentations.AdoCharacteristicZero

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The characteristic-zero Ado assertion of Proposition 10.2. -/
def characteristicZeroAdoType : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K]
    (G : Type v) [LieRing G] [LieAlgebra K G] [FiniteDimensional K G],
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module K V),
      FiniteDimensional K V ∧
        ∃ ρ : G →ₗ⁅K⁆ Module.End K V, Function.Injective ρ

end Specs.LieAlgebrasAndRepresentations.AdoCharacteristicZero
