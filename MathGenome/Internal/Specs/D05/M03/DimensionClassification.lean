import MathGenome.Internal.Specs.D05.M02.Dimension
import MathGenome.Internal.Specs.D05.M03.Isomorphism

/-!
Independent statements for K05.03.dimension_classification (paper.tex:574–580).

Both spaces are finite-dimensional over the same field. Dimension and
isomorphism retain the upstream canonical meanings, `Module.finrank` and
`LinearEquiv`. The zero spaces are included, and the two spaces may live in
different universes. Existence asserts no preferred choice of isomorphism.
-/

namespace Specs.D05.M03.DimensionClassification

/-- Finite-dimensional spaces are isomorphic exactly when their dimensions agree. -/
def isomorphic_iff_dimension_eq : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W],
    Nonempty (V ≃ₗ[K] W) ↔ Module.finrank K V = Module.finrank K W

/-- The same classification expressed using the source's bijective linear maps. -/
def exists_bijective_iff_dimension_eq : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W],
    (∃ T : V →ₗ[K] W, Function.Bijective T) ↔
      Module.finrank K V = Module.finrank K W

end Specs.D05.M03.DimensionClassification
