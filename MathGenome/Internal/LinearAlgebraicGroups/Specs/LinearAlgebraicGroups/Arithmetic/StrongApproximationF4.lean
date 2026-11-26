import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RealAlbertGroups

open LinearAlgebraicGroups.Arithmetic
open LinearAlgebraicGroups.Arithmetic.AdelicGroups
open LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
open LinearAlgebraicGroups.Specs.IntegralModels (MatrixRealization)

universe u v

namespace LinearAlgebraicGroups.Specs.StrongApproximationF4

/-- Every group of absolute type F₄ over a global field has strong approximation
away from any finite nonempty set whose product of local groups is noncompact. -/
def Statement : Prop :=
  ∀ {K : Type u} [Field K] (G : AffineAlgebraicGroup K),
    RealAlbertGroups.HasAbsoluteTypeF4 G →
    ∀ (D : GlobalFieldData.{u,v} K) (i : MatrixRealization G) (S : Finset D.Place),
      S.Nonempty → ¬ CompactSpace (FinitePoints D i S) → StrongApproximation D i S

end LinearAlgebraicGroups.Specs.StrongApproximationF4
