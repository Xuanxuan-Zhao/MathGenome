import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.PathAlgebra

/-! The independent specification of bounded-length path finiteness. -/

universe u v

namespace RM03.BoundedPathsSpec

def FinitePathsOfLengthLt : Prop :=
  ∀ {V : Type u} [Quiver.{v} V] [Finite V] [Finite (Arrow V)] (m : ℕ),
    Finite {p : Path V // p.length < m}

end RM03.BoundedPathsSpec
