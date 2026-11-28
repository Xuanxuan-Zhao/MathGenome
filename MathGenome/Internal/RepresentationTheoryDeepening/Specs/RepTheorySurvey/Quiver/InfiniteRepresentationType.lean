import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.Forms

/-! The dimension obstruction to finite representation type. -/

namespace RepTheorySurvey.Quiver.InfiniteRepresentationTypeSpec

universe u v w d

/-- A finite acyclic quiver whose real Tits form fails positive definiteness has
infinitely many isomorphism classes of indecomposable finite-dimensional
representations over every infinite field. -/
abbrev InfiniteIndecomposableClasses : Prop :=
  ∀ (k : Type w) {Q : Type u} [Field k] [Infinite k] [Quiver.{v} Q] [Fintype Q]
    [Fintype (RM03.Arrow Q)], ¬ RM03.HasOrientedCycle Q → ¬ FormsSpec.PositiveDefinite Q →
      Infinite (FormsSpec.IndecomposableClass.{u, v, w, max w d} k Q)

end RepTheorySurvey.Quiver.InfiniteRepresentationTypeSpec
