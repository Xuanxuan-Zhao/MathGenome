import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.IntegralModels
import Mathlib.Topology.Algebra.Group.Matrix

noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Topology
open LinearAlgebraicGroups.Specs
open scoped RestrictedProduct

universe u v

namespace LinearAlgebraicGroups.Arithmetic.AdelicGroups

open Specs.IntegralModels (MatrixRealization RationalPoints)
open Specs.Unipotent (Index)

variable {K : Type u} [Field K] {G : AffineAlgebraicGroup K}

/-- The group of points, with the realization retained as an index for the local topology. -/
def PointsIn (_i : MatrixRealization G) (R : Type u) [CommRing R] [Algebra K R] : Type u :=
  ((groupPointsFunctor K).obj G.val).obj (CommAlgCat.of K R)

instance (i : MatrixRealization G) (R : Type u) [CommRing R] [Algebra K R] :
    Group (PointsIn i R) :=
  inferInstanceAs (Group (((groupPointsFunctor K).obj G.val).obj (CommAlgCat.of K R)))

/-- The matrix of a point under the chosen closed realization. -/
def asMatrix (i : MatrixRealization G) (R : Type u) [CommRing R] [Algebra K R] :
    PointsIn i R →* Matrix.GeneralLinearGroup (Index.{u} i.size) R :=
  (i.matrix.hom.app (CommAlgCat.of K R)).hom.comp
    (((groupPointsFunctor K).map i.embedding).app (CommAlgCat.of K R)).hom

instance (i : MatrixRealization G) (R : Type u) [CommRing R] [Algebra K R] [TopologicalSpace R] :
    TopologicalSpace (PointsIn i R) :=
  TopologicalSpace.induced (asMatrix i R) inferInstance

def changePoints (i j : MatrixRealization G) (R : Type u) [CommRing R] [Algebra K R] :
    PointsIn i R ≃* PointsIn j R :=
  MulEquiv.refl (((groupPointsFunctor K).obj G.val).obj (CommAlgCat.of K R))

variable (D : GlobalFieldData.{u, v} K)

instance completionAlgebra (w : D.Place) : Algebra K (D.Completion w) :=
  (D.embedding w).toAlgebra

abbrev LocalPoints (i : MatrixRealization G) (w : D.Place) :=
  PointsIn i (D.Completion w)

/-- Points whose matrices come from invertible matrices over the local integers. -/
def integralPoints (i : MatrixRealization G) (w : D.FinitePlace) :
    Subgroup (LocalPoints D i (.inl w)) :=
  (Matrix.GeneralLinearGroup.map (D.integers w).subtype).range.comap
    (asMatrix i (D.Completion (.inl w)))

/-- Archimedean factors have no integrality restriction. -/
def localSubgroup (i : MatrixRealization G) (w : D.Place) : Subgroup (LocalPoints D i w) :=
  match w with
  | .inl w => integralPoints D i w
  | .inr _ => ⊤

abbrev Outside (S : Finset D.Place) := {w : D.Place // w ∉ S}

/-- The group of adeles away from S, with Mathlib's restricted product topology. -/
abbrev Adeles (i : MatrixRealization G) (S : Finset D.Place) :=
  Πʳ w : Outside D S, [LocalPoints D i w.1, localSubgroup D i w.1]

/-- Scalar extension of a rational point to one completion. -/
def localPoint (i : MatrixRealization G) (w : D.Place) :
    RationalPoints G →* LocalPoints D i w :=
  (((groupPointsFunctor K).obj G.val).map
    (CommAlgCat.ofHom (Algebra.ofId K (D.Completion w)))).hom

/-- Density of the diagonal in the group of adeles away from S. -/
def StrongApproximation (i : MatrixRealization G) (S : Finset D.Place) : Prop :=
  Dense {x : Adeles D i S | ∃ g : RationalPoints G, ∀ w : Outside D S, x w = localPoint D i w.1 g}

/-- Approximation in every finite product of completions. -/
def WeakApproximation (i : MatrixRealization G) : Prop :=
  ∀ T : Finset D.Place,
    DenseRange (fun g : RationalPoints G => fun w : (↑T : Set D.Place) =>
      localPoint D i w.1 g)

/-- A box of local sets, as a subset of the adelic group. -/
def box (i : MatrixRealization G) (S : Finset D.Place)
    (U : ∀ w : Outside D S, Set (LocalPoints D i w.1)) : Set (Adeles D i S) :=
  {x | ∀ w, x w ∈ U w}

/-- The basic boxes prescribe local open sets at finitely many places and the
given integral groups at every other finite place. -/
def basicBoxes (i : MatrixRealization G) (S : Finset D.Place) : Set (Set (Adeles D i S)) :=
  {B | ∃ (T : Finset (Outside D S)) (U : ∀ w : Outside D S, Set (LocalPoints D i w.1)),
    (∀ w, IsOpen (U w)) ∧
    (∀ w, w ∉ T → U w = localSubgroup D i w.1) ∧
    B = box D i S U}

end LinearAlgebraicGroups.Arithmetic.AdelicGroups

namespace LinearAlgebraicGroups.Specs.AdelicGroups

open Arithmetic Arithmetic.AdelicGroups
open LinearAlgebraicGroups.Specs.IntegralModels (MatrixRealization RationalPoints)

def localMatrixEmbedding : Prop :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u, v} K)
    (i : MatrixRealization G) (w : D.Place),
    Topology.IsClosedEmbedding (asMatrix i (D.Completion w))

def usualLocalTopology : Prop :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u, v} K)
    (i : MatrixRealization G) (w : D.Place),
    Topology.IsEmbedding (fun g : LocalPoints D i w => (asMatrix i (D.Completion w) g).val)

def integralCompactOpen : Prop :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u, v} K)
    (i : MatrixRealization G) (w : D.FinitePlace),
    IsCompact (integralPoints D i w : Set (LocalPoints D i (.inl w))) ∧
      IsOpen (integralPoints D i w : Set (LocalPoints D i (.inl w)))

def adelicTopology : Prop :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u, v} K)
    (i : MatrixRealization G) (S : Finset D.Place), IsTopologicalGroup (Adeles D i S)

def independence : Prop :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u, v} K)
    (i j : MatrixRealization G) (S : Finset D.Place),
    ∃! e : Adeles D i S ≃ₜ* Adeles D j S,
      ∀ (x : Adeles D i S) (w : Outside D S),
        e x w = changePoints i j (D.Completion w.1) (x w)

def adelicBasis : Prop :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u, v} K)
    (i : MatrixRealization G) (S : Finset D.Place), TopologicalSpace.IsTopologicalBasis (basicBoxes D i S)

set_option linter.checkUnivs false in
/-- Type of the canonical homomorphism to the restricted product. -/
def diagonalType :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u, v} K)
    (i : MatrixRealization G) (S : Finset D.Place), RationalPoints G →* Adeles D i S

def diagonalCoordinates (d : diagonalType.{u, v}) : Prop :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u, v} K)
    (i : MatrixRealization G) (S : Finset D.Place) (g : RationalPoints G) (w : Outside D S),
    d D i S g w = localPoint D i w.1 g

def canonicalDiagonal : Prop :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u, v} K)
    (i : MatrixRealization G) (S : Finset D.Place),
    ∃! d : RationalPoints G →* Adeles D i S,
      ∀ (g : RationalPoints G) (w : Outside D S), d g w = localPoint D i w.1 g

def strongApproximationDensity : Prop :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u, v} K)
    (i : MatrixRealization G) (S : Finset D.Place) (d : RationalPoints G →* Adeles D i S),
    (∀ (g : RationalPoints G) (w : Outside D S), d g w = localPoint D i w.1 g) →
    (StrongApproximation D i S ↔ DenseRange d)

end LinearAlgebraicGroups.Specs.AdelicGroups
