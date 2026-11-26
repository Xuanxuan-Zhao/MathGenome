import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.DiscreteDiagonals
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Topology.KrullDimension

universe u v

namespace LinearAlgebraicGroups.Specs.NoncompactnessNecessary

open AlgebraicGeometry Arithmetic Arithmetic.AdelicGroups
open Specs.IntegralModels (MatrixRealization RationalPoints)

abbrev InsidePoints {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (S : Finset D.Place) :=
  ∀ w : (↑S : Set D.Place), LocalPoints D i w.1

def outsideDiagonalImage {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (S : Finset D.Place) :
    Set (Adeles D i S) :=
  {x | ∃ g : RationalPoints G, ∀ w : Outside D S, x w = localPoint D i w.1 g}

/-- Compactness of the omitted local groups forces the projected diagonal to remain
closed and discrete, for any affine algebraic group. -/
def CompactInsideClosedDiscrete : Prop :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (S : Finset D.Place),
    CompactSpace (InsidePoints D i S) →
      IsClosed (outsideDiagonalImage D i S) ∧ IsDiscrete (outsideDiagonalImage D i S)

/-- The compactness obstruction for positive-dimensional connected smooth affine groups,
in particular the connected absolutely almost simple groups of F12. -/
def CompactInsidePrecludesStrongApproximation : Prop :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (S : Finset D.Place),
    S.Nonempty → Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    0 < topologicalKrullDim G.val.X.left →
    CompactSpace (InsidePoints D i S) →
      IsClosed (outsideDiagonalImage D i S) ∧ IsDiscrete (outsideDiagonalImage D i S) ∧
        ¬ StrongApproximation D i S

end LinearAlgebraicGroups.Specs.NoncompactnessNecessary
