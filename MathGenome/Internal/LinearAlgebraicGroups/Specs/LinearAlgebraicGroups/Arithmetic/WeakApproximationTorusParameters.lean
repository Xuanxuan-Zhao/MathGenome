import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TorusNormCovers
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.WeakApproximationTorusParameters

noncomputable section

/-- The principal open defined by a polynomial on affine space over the ground field. -/
abbrev PrincipalOpen {k : Type u} [Field k] {σ : Type u} (p : MvPolynomial σ k) :
    SchemeOver k :=
  Specs.TorusNormCovers.PrincipalOpen p

end

end LinearAlgebraicGroups.Arithmetic.WeakApproximationTorusParameters

namespace LinearAlgebraicGroups.Specs.WeakApproximationTorusParameters

open Arithmetic.WeakApproximationTorusParameters
open GeometricRadicals (IsSemisimple)

/-- A pointed smooth parametrization of a connected semisimple group in characteristic zero. -/
def SmoothPointedParametrization : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (G : AffineAlgebraicGroup k), IsSemisimple G →
    ∃ (n : ℕ) (p : MvPolynomial (ULift.{u} (Fin n)) k)
      (a : Points (PrincipalOpen p) (CommAlgCat.of k k))
      (f : PrincipalOpen p ⟶ G.val.X), a ≫ f = (1 : Points G.val.X (CommAlgCat.of k k)) ∧ Smooth f.left

end LinearAlgebraicGroups.Specs.WeakApproximationTorusParameters
