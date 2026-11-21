import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.PathAlgebra

/-! The finite-dimensionality assertion of RM03-C06.03. -/

universe u v w

namespace RM03

/-- An oriented cycle is a positive-length closed path whose vertices are distinct
after omitting the final copy of its starting vertex. -/
def HasOrientedCycle (V : Type u) [Quiver.{v} V] : Prop :=
  ∃ (i : V) (p : Quiver.Path i i), 0 < p.length ∧ p.vertices.dropLast.Nodup

namespace AcyclicFinitenessSpec

def FiniteDimensionalIffNoOrientedCycle : Prop :=
  ∀ {k : Type w} {V : Type u} [Field k] [Quiver.{v} V]
    [Finite V] [Nonempty V] [Finite (Arrow V)],
    FiniteDimensional k (PathAlgebraSpec.Carrier k V) ↔ ¬ HasOrientedCycle V

end AcyclicFinitenessSpec
end RM03
