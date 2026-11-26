import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals

open AlgebraicGeometry

universe u

namespace LinearAlgebraicGroups.Specs.MaximalToriExist

open GeometricRadicals (IsTorus IsMaximalTorus baseChangedSubgroup)

/-- Every smooth connected affine algebraic group over a field has a torus
whose base change to the algebraic closure is maximal. -/
def GeometricallyMaximalTorusExists : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∃ T : ClosedSubgroup G.val, IsTorus T.group ∧
      ∃ h : IsClosedImmersion
          ((groupBaseChange k (AlgebraicClosure k)).map T.inclusion).hom.hom.left,
        IsMaximalTorus (baseChangedSubgroup (AlgebraicClosure k) T h)

end LinearAlgebraicGroups.Specs.MaximalToriExist
