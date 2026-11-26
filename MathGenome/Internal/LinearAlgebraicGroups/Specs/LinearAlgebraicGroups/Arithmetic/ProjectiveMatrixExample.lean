import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

noncomputable section

open Matrix Topology
open scoped MatrixGroups RestrictedProduct

namespace LinearAlgebraicGroups.Arithmetic.ProjectiveMatrixExample

abbrev Mat (R : Type*) := Matrix (Fin 2) (Fin 2) R

abbrev MatrixAut (R : Type*) [CommRing R] := Mat R ≃ₐ[R] Mat R

def matrixConjugation {R : Type*} [CommRing R] (G : GL (Fin 2) R) : MatrixAut R where
  toFun X := (G : Mat R) * X * (↑G⁻¹ : Mat R)
  invFun X := (↑G⁻¹ : Mat R) * X * (G : Mat R)
  left_inv X := by simp [← mul_assoc]
  right_inv X := by simp [← mul_assoc]
  map_mul' X Y := by simp [mul_assoc]
  map_add' X Y := by rw [mul_add, add_mul]
  commutes' r := by rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

@[simp] theorem matrixConjugation_apply {R : Type*} [CommRing R] (G : GL (Fin 2) R) (X : Mat R) :
    matrixConjugation G X = (G : Mat R) * X * (↑G⁻¹ : Mat R) := rfl

def conjugation {R : Type*} [CommRing R] : PGL(2, R) →* MatrixAut R :=
  ProjGenLinGroup.lift
    { toFun := matrixConjugation
      map_one' := AlgEquiv.ext fun X => by simp
      map_mul' G H := AlgEquiv.ext fun X => by
        simp [_root_.mul_inv_rev, mul_assoc] }
    (MonoidHom.ext fun u => AlgEquiv.ext fun X => by
      change (GeneralLinearGroup.scalar (Fin 2) u : Mat R) * X *
        (↑((GeneralLinearGroup.scalar (Fin 2)) u)⁻¹ : Mat R) = X
      rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_comm _ (Commute.all _),
        ← GeneralLinearGroup.coe_scalar u, mul_assoc, Units.mul_inv, mul_one])

@[simp] theorem conjugation_mk {R : Type*} [CommRing R] (G : GL (Fin 2) R) :
    conjugation (ProjGenLinGroup.mk G) = matrixConjugation G := rfl

/-- The entries of the conjugation representation in the basis of matrix units. -/
def coordinates {R : Type*} [CommRing R] (a : MatrixAut R) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R :=
  fun i j => a (Matrix.single j.1 j.2 1) i.1 i.2

/-- A matrix of coefficients acting on `Mat R` in the matrix-unit basis. -/
def coordinateAction {R : Type*} [CommRing R]
    (C : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R) : Mat R →ₗ[R] Mat R :=
  Matrix.toLin (Matrix.stdBasis R (Fin 2) (Fin 2)) (Matrix.stdBasis R (Fin 2) (Fin 2)) C

/-- The equations cutting out matrix algebra automorphisms in the ambient general linear group. -/
def algebraEquations {R : Type*} [CommRing R] (C : GL (Fin 2 × Fin 2) R) : Prop :=
  let L := coordinateAction C.val
  L 1 = 1 ∧ ∀ (i j : Fin 2 × Fin 2),
    L (Matrix.single i.1 i.2 1 * Matrix.single j.1 j.2 1) =
      L (Matrix.single i.1 i.2 1) * L (Matrix.single j.1 j.2 1)

instance {R : Type*} [CommRing R] [TopologicalSpace R] :
    TopologicalSpace PGL(2, R) :=
  inferInstanceAs (TopologicalSpace (GL (Fin 2) R ⧸ Subgroup.center (GL (Fin 2) R)))

abbrev Prime := {p : ℕ // p.Prime}

instance (p : Prime) : Fact (p.val.Prime) := ⟨p.property⟩

def five : Prime := ⟨5, by decide⟩

/-- The scalar classes represented by invertible integral matrices. -/
def integralClasses (p : Prime) : Subgroup PGL(2, ℚ_[p.val]) :=
  (ProjGenLinGroup.map PadicInt.Coe.ringHom).range

/-- Extension of scalars on rational projective matrix classes. -/
def localClass (p : Prime) : PGL(2, ℚ) →* PGL(2, ℚ_[p.val]) :=
  ProjGenLinGroup.map (Rat.castHom _)

/-- The determinant of a representative lies in the trivial square class. -/
def squareDet {R : Type*} [CommRing R] (g : PGL(2, R)) : Prop :=
  ∃ A : GL (Fin 2) R, ProjGenLinGroup.mk A = g ∧ IsSquare (A.det : R)

abbrev FiniteAdeles := Πʳ p : Prime, [PGL(2, ℚ_[p.val]), integralClasses p]

/-- All coordinates are integral, and the determinant at 5 has nonsquare unit class. -/
def obstruction : Set FiniteAdeles :=
  {x | (∀ p : Prime, x p ∈ integralClasses p) ∧ ¬ squareDet (x five)}

end LinearAlgebraicGroups.Arithmetic.ProjectiveMatrixExample

namespace LinearAlgebraicGroups.Specs.ProjectiveMatrixExample

open Arithmetic.ProjectiveMatrixExample

/-- A local point of the conjugation model has a matrix representative, unique up to a unit scalar. -/
def LocalConjugation : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R],
    Function.Bijective (conjugation : PGL(2, R) → MatrixAut R)

/-- The integral conjugation model is the group of algebra automorphisms, with
its matrix realization given by the algebra equations over every test ring. -/
def ConjugationModel : Prop :=
  ∀ (R : Type) [CommRing R],
    (∀ a : MatrixAut R, ∃ C : GL (Fin 2 × Fin 2) R,
      C.val = coordinates a ∧ C.inv = coordinates a.symm) ∧
    ∀ C : GL (Fin 2 × Fin 2) R,
      algebraEquations C ↔ ∃! a : MatrixAut R, coordinates a = C.val

/-- The scalar quotient has the ordinary topology of the conjugation realization. -/
def ConjugationTopology : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [T2Space F] [IsTopologicalRing F]
    [ContinuousInv₀ F],
    IsEmbedding (fun g : PGL(2, F) => coordinates (conjugation g))

/-- An invertible conjugation matrix over the local integers represents exactly an integral class.
The two matrices in the condition are the action and its inverse on the matrix-unit basis. -/
def IntegralConjugation : Prop :=
  ∀ (p : Prime) (g : PGL(2, ℚ_[p.val])),
    g ∈ integralClasses p ↔
      ∀ i j, ‖coordinates (conjugation g) i j‖ ≤ 1 ∧
             ‖coordinates (conjugation g⁻¹) i j‖ ≤ 1

def SquareClass : Prop :=
  ∀ (F : Type) [Field F] (A : GL (Fin 2) F),
    squareDet (ProjGenLinGroup.mk A) ↔ IsSquare (A.det : F)

def RealNoncompact : Prop := ¬ IsCompact (Set.univ : Set PGL(2, ℝ))

def RationalDiagonal : Prop :=
  ∃ d : PGL(2, ℚ) →* FiniteAdeles, ∀ g p, d g p = localClass p g

def EvenValuations : Prop :=
  ∀ (A : GL (Fin 2) ℚ), (∀ p : Prime, localClass p (ProjGenLinGroup.mk A) ∈ integralClasses p) →
    (∀ p : ℕ, p.Prime → Even (padicValRat p (A.det : ℚ))) ∧
    (IsSquare (A.det : ℚ) ∨ IsSquare (-(A.det : ℚ)))

def AdelicObstruction : Prop :=
  IsOpen obstruction ∧ obstruction.Nonempty ∧
    ∀ x ∈ obstruction, ¬ ∃ g : PGL(2, ℚ), ∀ p, x p = localClass p g

end LinearAlgebraicGroups.Specs.ProjectiveMatrixExample
