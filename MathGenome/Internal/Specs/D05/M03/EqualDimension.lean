import MathGenome.Internal.Specs.D05.M03.Isomorphism
import MathGenome.Internal.Specs.D05.M03.RankNullity
import MathGenome.Internal.Specs.D05.M02.SubspaceDimension

/-!
Independent statements for K05.03.equal_dimension (paper.tex:582–588).

Both spaces are finite-dimensional over the same arbitrary field, and their
natural-number dimensions agree. This is exactly the existence of a common
finite dimension `n`; no positivity or nonzero-space hypothesis is imposed.
Invertibility concerns the given map `T`, rather than the mere existence of
some isomorphism between its domain and codomain. It is expressed both by a
linear equivalence whose underlying map is `T` and by a unique two-sided
linear inverse. The last statement spells out the source's zero-space case.
-/

namespace Specs.D05.M03.EqualDimension

/-- Injectivity, surjectivity, and invertibility of a map between spaces of
equal finite dimension are equivalent. The inverse is linear and unique. -/
def equal_dimension : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    [FiniteDimensional K W] (T : V →ₗ[K] W),
    Module.finrank K V = Module.finrank K W →
      (Function.Injective T ↔ Function.Surjective T) ∧
      (Function.Injective T ↔ ∃ e : V ≃ₗ[K] W, e.toLinearMap = T) ∧
      (Function.Surjective T ↔ ∃! S : W →ₗ[K] V,
        S.comp T = LinearMap.id ∧ T.comp S = LinearMap.id)

/-- In dimension zero there is only one linear map, and that map is the
underlying map of exactly one linear isomorphism. -/
def zero_dimensional_unique : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    [FiniteDimensional K W] (T : V →ₗ[K] W),
    Module.finrank K V = 0 → Module.finrank K W = 0 →
      (∀ S : V →ₗ[K] W, S = T) ∧
      ∃! e : V ≃ₗ[K] W, e.toLinearMap = T

end Specs.D05.M03.EqualDimension
