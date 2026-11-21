import Mathlib.LinearAlgebra.LinearIndependent.Defs
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Density.Action

universe u v

namespace RM03.Specs.Density

/-- RM03-C03.01. Right linear independence over the opposite endomorphism ring
is expressed as left linear independence over the endomorphism ring acting by evaluation. -/
def interpolateType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] (n : ℕ) (x y : Fin n → M),
    LinearIndependent (Module.End R M) x → ∃ r : R, ∀ i : Fin n, r • x i = y i

end RM03.Specs.Density
