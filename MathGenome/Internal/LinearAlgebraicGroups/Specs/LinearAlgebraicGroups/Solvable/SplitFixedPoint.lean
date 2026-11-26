import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.FixedPointSchemes
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
import Mathlib.AlgebraicGeometry.Morphisms.Proper

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory

universe u

namespace LinearAlgebraicGroups.Specs

/-- A split solvable affine group acting on a proper scheme with a rational
point has a rational point in the scheme-theoretic fixed locus. -/
def SplitSolvableFixedPoint : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (X : SchemeOver k) (act : ModObj G.val.X X),
    SchemeDerivedGroup.IsSplitSolvable G.val → IsProper X.hom →
    Nonempty ((𝟙_ (SchemeOver k)) ⟶ X) →
    ∃ (Z : SchemeOver k) (i : Z ⟶ X),
      IsClosedImmersion i.left ∧ RepresentsFixedPoints act.smul i ∧
        Nonempty ((𝟙_ (SchemeOver k)) ⟶ Z)

end LinearAlgebraicGroups.Specs
