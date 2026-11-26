import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.SplitFixedPoint

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory

universe u

namespace LinearAlgebraicGroups.Specs.BorelFixedPoint

/-- The Borel fixed-point theorem for split solvable groups over any field. -/
def Split : Prop := SplitSolvableFixedPoint.{u}

/-- A smooth connected solvable affine group over an algebraically closed field
has a rational point in the scheme-theoretic fixed locus of any action on a
nonempty proper scheme over that field. -/
def OverAlgClosed : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (X : SchemeOver k) (act : ModObj G.val.X X),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    SchemeDerivedGroup.IsSolvable G.val → IsProper X.hom → Nonempty X.left →
    ∃ (Z : SchemeOver k) (i : Z ⟶ X),
      IsClosedImmersion i.left ∧ RepresentsFixedPoints act.smul i ∧
        Nonempty ((𝟙_ (SchemeOver k)) ⟶ Z)

end LinearAlgebraicGroups.Specs.BorelFixedPoint
