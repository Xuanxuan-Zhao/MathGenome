import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

open AlgebraicGeometry CategoryTheory Filter
open scoped Topology

noncomputable section

universe u v

namespace LinearAlgebraicGroups.Arithmetic.WeakApproximationLocalSmoothImage

/-- The principal open of affine space obtained by inverting the given polynomial. -/
abbrev PrincipalOpen {K : Type u} [Field K] {n : ℕ}
    (p : MvPolynomial (ULift.{u} (Fin n)) K) : SchemeOver K :=
  (testSpec K).obj (Opposite.op (CommAlgCat.of K (Localization.Away p)))

/-- The canonical global field data for a number field. -/
abbrev numberData (K : Type u) [Field K] [NumberField K] : GlobalFieldData.{u, v} K :=
  .number inferInstance

end LinearAlgebraicGroups.Arithmetic.WeakApproximationLocalSmoothImage

namespace LinearAlgebraicGroups.Specs.WeakApproximationLocalSmoothImage

open Arithmetic AdelicGroups Arithmetic.WeakApproximationLocalSmoothImage
open IntegralModels (MatrixRealization)

/-- A smooth principal-open parameter map has a local image neighborhood of the
specialization of the image of every rational parameter at every place. -/
def LocalSmoothImageFor {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K) : Prop :=
  ∀ (G : AffineAlgebraicGroup K),
    Smooth G.val.X.hom → ∀ (i : MatrixRealization G) {n : ℕ}
      (p : MvPolynomial (ULift.{u} (Fin n)) K) (f : PrincipalOpen p ⟶ G.val.X),
      Smooth f.left → ∀ (a : Points (PrincipalOpen p) (CommAlgCat.of K K))
        (w : D.Place),
        Set.range (fun b : Points (PrincipalOpen p)
            (CommAlgCat.of K (D.Completion w)) =>
            (b ≫ f : LocalPoints D i w)) ∈
          𝓝 (localPoint D i w (a ≫ f))

def LocalSmoothImage : Prop :=
  ∀ {K : Type u} [Field K] [NumberField K], LocalSmoothImageFor (numberData.{u, v} K)

end LinearAlgebraicGroups.Specs.WeakApproximationLocalSmoothImage
