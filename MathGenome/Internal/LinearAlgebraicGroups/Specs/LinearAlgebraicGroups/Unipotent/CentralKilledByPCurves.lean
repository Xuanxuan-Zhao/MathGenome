import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.Stabilizers
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.Criteria
import Mathlib.FieldTheory.TranscendentalSeparable
import Mathlib.FieldTheory.Galois.Basic

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.Unipotent

noncomputable section

variable {k : Type u} [Field k]

/-- A morphism from the affine line, with no homomorphism condition. -/
abbrev AffineLineCurve (G : GroupScheme k) :=
  Points G.X (CommAlgCat.of k (Polynomial k))

/-- The point of a curve at the origin. -/
def curveAtZero {G : GroupScheme k} (x : AffineLineCurve G) :
    Points G.X (CommAlgCat.of k k) :=
  mapPoints (CommAlgCat.ofHom (Polynomial.aeval (0 : k))) x

/-- Regard a rational point as a constant curve. -/
def constantCurve {G : GroupScheme k} (x : Points G.X (CommAlgCat.of k k)) :
    AffineLineCurve G :=
  mapPoints (CommAlgCat.ofHom (Algebra.ofId k (Polynomial k))) x

/-- A curve is constant exactly when it agrees with the constant curve at its origin. -/
def IsNonconstantCurve {G : GroupScheme k} (x : AffineLineCurve G) : Prop :=
  x ≠ constantCurve (curveAtZero x)

/-- The power condition is imposed on all test algebras, including nonreduced ones. -/
def IsKilledBy (p : ℕ) (G : GroupScheme k) : Prop :=
  ∀ (R : TestAlgebra k) (x : Points G.X R), x ^ p = 1

/-- A curve after a separable extension gives a normalized nonconstant curve
in a smooth connected central subgroup killed by the characteristic. -/
def CentralKilledByPCurves : Prop :=
  ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (U : AffineAlgebraicGroup k), Smooth U.val.X.hom → ConnectedSpace U.val.X.left →
    IsUnipotent U →
    (∀ (L : Type u) [Field L] [Algebra k L] [Algebra.IsTranscendentalSeparable k L],
      ∀ x : AffineLineCurve ((groupBaseChange k L).obj U.val), IsNonconstantCurve x →
      ∃ F : ClosedSubgroup U.val,
        Smooth F.group.X.hom ∧ ConnectedSpace F.group.X.left ∧
        Centralizes (𝟙 U.val) F.inclusion.hom.hom ∧ IsKilledBy p F.group ∧
        ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : FiniteDimensional k K)
          (_ : IsGalois k K) (y : AffineLineCurve ((groupBaseChange k K).obj F.group)),
          curveAtZero y = 1 ∧ IsNonconstantCurve y)

end

end LinearAlgebraicGroups.Specs.Unipotent
