import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import Mathlib.AlgebraicGeometry.Morphisms.Finite

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v

namespace LinearAlgebraicGroups.Arithmetic.FiniteAdelicMorphism

open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.IntegralModels (MatrixRealization)
open AdelicGroups

variable {K : Type u} [Field K] {G Q : AffineAlgebraicGroup K}

/-- The homomorphism on points obtained by applying the group scheme map to a test algebra. -/
def pointsMap (q : G.val ⟶ Q.val) (i : MatrixRealization G) (j : MatrixRealization Q)
    (R : Type u) [CommRing R] [Algebra K R] : PointsIn i R →* PointsIn j R :=
  (((groupPointsFunctor K).map q).app (CommAlgCat.of K R)).hom

end LinearAlgebraicGroups.Arithmetic.FiniteAdelicMorphism

namespace LinearAlgebraicGroups.Specs.FiniteAdelicMorphism

open Arithmetic Arithmetic.AdelicGroups
open Arithmetic.FiniteAdelicMorphism (pointsMap)
open IntegralModels (MatrixRealization)

/-- A continuous homomorphism with the given local maps and compact inverse images. -/
def HasProperAdelicMap {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K)
    {G Q : AffineAlgebraicGroup K} (q : G.val ⟶ Q.val)
    (i : MatrixRealization G) (j : MatrixRealization Q) : Prop :=
    ∃ f : Adeles D i ∅ →* Adeles D j ∅,
      (∀ (x : Adeles D i ∅) (w : Outside D ∅),
        f x w = pointsMap q i j (D.Completion w.1) (x w)) ∧
      Continuous f ∧
      ∀ C : Set (Adeles D j ∅), IsCompact C → IsCompact (f ⁻¹' C)

/-- A finite homomorphism induces a map on the full adelic groups of a number field
whose inverse image of every compact subset is compact. -/
def finiteAdelicMorphism : Prop :=
  ∀ {K : Type u} [Field K] [h : NumberField K] {G Q : AffineAlgebraicGroup K}
    (q : G.val ⟶ Q.val) (_ : IsFinite q.hom.hom.left)
    (i : MatrixRealization G) (j : MatrixRealization Q),
    HasProperAdelicMap (.number.{u, v} h) q i j

end LinearAlgebraicGroups.Specs.FiniteAdelicMorphism
