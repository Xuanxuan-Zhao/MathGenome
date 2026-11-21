import MathGenome.Internal.Specs.D05.M02.Dimension
import MathGenome.Internal.Specs.D05.M02.SumIntersection

/-!
Independent statement of K05.02.grassmann (paper.tex:514–521).

Dimension is the canonical `Module.finrank` used in the upstream dimension
interface. The sum is the submodule supremum, whose carrier is the paper's
set of sums by `sum_eq_sup` in the upstream sum/intersection interface;
the infimum is the intersection with its inherited vector-space structure.
Only the two subspaces are assumed finite-dimensional. In particular, the
ambient space is unrestricted, and zero subspaces are included.
-/

namespace Specs.D05.M02.Grassmann

/-- The dimension formula for the sum and intersection of two finite-dimensional
subspaces, over an arbitrary field. -/
def grassmann : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U W : Submodule K V) [FiniteDimensional K U] [FiniteDimensional K W],
    Module.finrank K (U ⊔ W : Submodule K V) +
        Module.finrank K (U ⊓ W : Submodule K V) =
      Module.finrank K U + Module.finrank K W

end Specs.D05.M02.Grassmann
