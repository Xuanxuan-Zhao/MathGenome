import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SteinbergGeometricFibres
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.MaximalToriExist

open AlgebraicGeometry CategoryTheory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory

universe u

namespace LinearAlgebraicGroups.Specs.RationalStronglyRegularElements

open _root_.LinearAlgebraicGroups.Affine (IsRationalJordanDecomposition RationalPoints)
open GeometricRadicals (GeometricGroup IsMaximalTorus IsReductive IsTorus baseChangedSubgroup)
open SteinbergGeometricFibres (IsPointCentralizer)

/-- A connected reductive group over an infinite field has a rational semisimple
point whose full centralizer is a geometrically maximal torus. -/
def ExistsRationalStronglyRegularElement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (H : AffineAlgebraicGroup k), IsReductive H →
    ∃ (T : ClosedSubgroup H.val), IsTorus T.group ∧
      (∃ h : IsClosedImmersion
        ((groupBaseChange k (AlgebraicClosure k)).map T.inclusion).hom.hom.left,
        IsMaximalTorus (baseChangedSubgroup (AlgebraicClosure k) T h)) ∧
      ∃ (t : 𝟙_ (SchemeOver k) ⟶ T.group.X) (y : 𝟙_ (SchemeOver k) ⟶ H.val.X),
        y = t ≫ T.inclusion.hom.hom ∧ IsPointCentralizer T y ∧
        (∀ (K : Type u) [Field K] [Algebra k K],
          ∃ h, IsPointCentralizer (scalarExtendedSubgroup K T h)
            (scalarExtendedRationalPoint K y)) ∧
        let ybar : RationalPoints (GeometricGroup H).val :=
          toUnit _ ≫ scalarExtendedRationalPoint (AlgebraicClosure k) y
        IsRationalJordanDecomposition ⟨(GeometricGroup H).val, (GeometricGroup H).property.1⟩
          ybar ybar 1

end LinearAlgebraicGroups.Specs.RationalStronglyRegularElements
