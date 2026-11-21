import MathGenome.Internal.Specs.D05.M03.Image
import MathGenome.Internal.Specs.D05.M07.DualMap

/-!
Independent statements for K05.07.dual_rank (paper.tex:1055–1064).

All three assertions concern a linear map between two finite-dimensional spaces
over the same arbitrary field. The dual map is ordinary precomposition on
`Module.Dual`, without topology or conjugation. Rank means the natural-number
dimension of the image, as in K05.03.image. No nonzero-dimension assumption is
made, so the zero spaces and zero map are included.
-/

namespace Specs.D05.M07.DualRank

/-- The algebraic transpose has the same rank as the original map. -/
def rank_dualMap : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (T : V →ₗ[K] W),
    Module.finrank K (LinearMap.range T.dualMap) =
      Module.finrank K (LinearMap.range T)

/-- Injectivity of the original map is equivalent to surjectivity of pullback. -/
def injective_iff_dualMap_surjective : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (T : V →ₗ[K] W),
    Function.Injective T ↔ Function.Surjective T.dualMap

/-- Surjectivity of the original map is equivalent to injectivity of pullback. -/
def surjective_iff_dualMap_injective : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (T : V →ₗ[K] W),
    Function.Surjective T ↔ Function.Injective T.dualMap

end Specs.D05.M07.DualRank
