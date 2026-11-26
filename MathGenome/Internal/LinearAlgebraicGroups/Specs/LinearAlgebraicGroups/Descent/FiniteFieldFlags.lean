import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
import Mathlib.FieldTheory.Finite.Basic

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.FiniteFieldFlags

open GeometricBorelConjugacy (IsKBorel IsQuasiSplit)
open GeometricRadicals (IsTorus IsMaximalTorus IsReductive baseChangedSubgroup)

/-- A smooth connected affine algebraic group over a finite field has a
closed subgroup over that field which is a Borel over the algebraic closure. -/
def RationalBorelExists : Prop :=
  ∀ {k : Type u} [Field k] [Fintype k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∃ B : ClosedSubgroup G.val, IsKBorel B

/-- A smooth connected affine algebraic group over a finite field has a
torus over that field which is maximal in the geometric group. -/
def GeometricallyMaximalTorusExists : Prop :=
  ∀ {k : Type u} [Field k] [Fintype k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∃ T : ClosedSubgroup G.val, IsTorus T.group ∧
      ∃ h : IsClosedImmersion
          ((groupBaseChange k (AlgebraicClosure k)).map T.inclusion).hom.hom.left,
        IsMaximalTorus (baseChangedSubgroup (AlgebraicClosure k) T h)

/-- Every connected reductive group over a finite field is quasi-split. -/
def ReductiveQuasiSplit : Prop :=
  ∀ {k : Type u} [Field k] [Fintype k] (G : AffineAlgebraicGroup k),
    IsReductive G → IsQuasiSplit G

end LinearAlgebraicGroups.Specs.FiniteFieldFlags
