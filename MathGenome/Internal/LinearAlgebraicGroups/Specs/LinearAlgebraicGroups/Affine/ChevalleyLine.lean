import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.ClosedSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.StandardGroups
import Mathlib.LinearAlgebra.Matrix.ToLin

open CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs

/-- Equality of the image and the base-changed line in the standard basis.
The coordinate vector with a `1` at index `i` spans the line. -/
def StabilizesCoordinateLine {R ι : Type u} [CommRing R] [Fintype ι] [DecidableEq ι]
    (m : Matrix.GeneralLinearGroup ι R) (i : ι) : Prop :=
  let line := Submodule.span R {Pi.single i (1 : R)}
  line.map (Matrix.toLin' m.val) = line

/-- Chevalley's theorem for closed subgroup schemes of finite-type affine groups.
The line is the span of a single vector in a finite basis of the rational module.
The factorization condition is imposed over every commutative test algebra. -/
def ChevalleyLine : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (H : ClosedSubgroup G.val),
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (i : ι)
      (L : AffineAlgebraicGroup k)
      (e : (groupPointsFunctor k).obj L.val ≅ StandardGroups.generalLinearPoints k ι)
      (f : G.val ⟶ L.val),
      ∀ (R : TestAlgebra k) (g : Points G.val.X R),
        StabilizesCoordinateLine
          (e.hom.app R (((groupPointsFunctor k).map f).app R g)) i ↔
          ∃ h : Points H.group.X R, h ≫ H.inclusion.hom.hom = g

end LinearAlgebraicGroups.Specs
