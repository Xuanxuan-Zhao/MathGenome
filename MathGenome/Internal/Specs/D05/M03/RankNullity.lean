import MathGenome.Internal.Specs.D05.M03.Kernel
import MathGenome.Internal.Specs.D05.M03.Image

/-!
Independent statement for K05.03.rank_nullity (paper.tex:561–569).

All spaces have the same scalar field. Only the domain is assumed finite-dimensional;
the kernel and image are the canonical submodules from the prerequisite interfaces.
Their dimensions are Mathlib's natural-number dimensions, as in K05.02.dimension.
In particular, the codomain may be infinite-dimensional and the domain may be zero.
-/

namespace Specs.D05.M03.RankNullity

/-- Dimension of the domain equals nullity plus rank. -/
def rank_nullity : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] (T : V →ₗ[K] W),
    Module.finrank K V =
      Module.finrank K (LinearMap.ker T) + Module.finrank K (LinearMap.range T)

end Specs.D05.M03.RankNullity
