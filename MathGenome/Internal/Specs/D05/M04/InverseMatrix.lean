import MathGenome.Internal.Specs.D05.M04.Composition
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
Independent statements for K05.04.inverse_matrix, paper.tex:644–650.
We reuse the accepted column action and matrix/map correspondence. All sizes
include zero. The square assertions are also proved over a commutative ring;
this includes the paper's field case. The rectangular versions retain separate
identities on the domain and codomain. No inverse identities are assumed merely
from the notation `A⁻¹`: each use has a bijectivity or inverse hypothesis.
-/

namespace Specs.D05.M04.InverseMatrix

/-- Two matrix inverse identities are exactly the two composition identities
for their actions on columns, including rectangular matrices. -/
def coordinate_inverse_iff : Prop :=
  ∀ {R : Type*} [CommRing R] {n m : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R),
    (B * A = 1 ∧ A * B = 1) ↔
      (MatrixOfMap.coordinateLinearMap_value B).comp
          (MatrixOfMap.coordinateLinearMap_value A) = LinearMap.id ∧
      (MatrixOfMap.coordinateLinearMap_value A).comp
          (MatrixOfMap.coordinateLinearMap_value B) = LinearMap.id

/-- The source's square-matrix invertibility criterion. -/
def inverse_iff_bijective : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R),
    (∃ B : Matrix (Fin n) (Fin n) R, B * A = 1 ∧ A * B = 1) ↔
      Function.Bijective (MatrixOfMap.coordinateLinearMap_value A)

/-- The same correspondence with independently indexed input and output. -/
def rectangular_inverse_iff_bijective : Prop :=
  ∀ {R : Type*} [CommRing R] {n m : ℕ} (A : Matrix (Fin m) (Fin n) R),
    (∃ B : Matrix (Fin n) (Fin m) R, B * A = 1 ∧ A * B = 1) ↔
      Function.Bijective (MatrixOfMap.coordinateLinearMap_value A)

/-- A left inverse and a right inverse must agree; in particular two
two-sided inverses agree. This argument also applies to rectangular shapes. -/
def inverse_unique : Prop :=
  ∀ {R : Type*} [CommRing R] {n m : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B C : Matrix (Fin n) (Fin m) R),
    B * A = 1 → A * C = 1 → B = C

/-- Bijectivity supplies a unique two-sided inverse, not an assumed one. -/
def inverse_exists_unique : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R),
    Function.Bijective (MatrixOfMap.coordinateLinearMap_value A) →
      ∃! B : Matrix (Fin n) (Fin n) R, B * A = 1 ∧ A * B = 1

/-- In arbitrary finite ordered bases, inverse matrices correspond exactly
to inverse linear maps. The reverse map uses the reversed pair of bases. -/
def matrix_inverse_iff : Prop :=
  ∀ {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] {n m : ℕ}
    (b : Module.Basis (Fin n) R V) (c : Module.Basis (Fin m) R W)
    (T : V →ₗ[R] W) (S : W →ₗ[R] V),
    (MatrixOfMap.matrixOfMap_value c b S * MatrixOfMap.matrixOfMap_value b c T = 1 ∧
      MatrixOfMap.matrixOfMap_value b c T * MatrixOfMap.matrixOfMap_value c b S = 1) ↔
      S.comp T = LinearMap.id ∧ T.comp S = LinearMap.id

/-- The matrix of the inverse linear equivalence satisfies both inverse
identities, including when the two bases have independently specified sizes. -/
def matrix_of_inverse : Prop :=
  ∀ {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] {n m : ℕ}
    (b : Module.Basis (Fin n) R V) (c : Module.Basis (Fin m) R W)
    (e : V ≃ₗ[R] W),
    MatrixOfMap.matrixOfMap_value c b e.symm.toLinearMap *
        MatrixOfMap.matrixOfMap_value b c e.toLinearMap = 1 ∧
      MatrixOfMap.matrixOfMap_value b c e.toLinearMap *
        MatrixOfMap.matrixOfMap_value c b e.symm.toLinearMap = 1

/-- For a square representation, the conventional nonsingular inverse is
exactly the matrix of the inverse map in the reversed bases. -/
def inverse_matrix : Prop :=
  ∀ {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] {n : ℕ}
    (b : Module.Basis (Fin n) R V) (c : Module.Basis (Fin n) R W)
    (e : V ≃ₗ[R] W),
    (MatrixOfMap.matrixOfMap_value b c e.toLinearMap)⁻¹ =
      MatrixOfMap.matrixOfMap_value c b e.symm.toLinearMap

/-- A bijective column action has a linear inverse, and its matrix is `A⁻¹`. -/
def inverse_represents : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R),
    Function.Bijective (MatrixOfMap.coordinateLinearMap_value A) →
      ∃ e : (Fin n → R) ≃ₗ[R] (Fin n → R),
        e.toLinearMap = MatrixOfMap.coordinateLinearMap_value A ∧
        e.symm.toLinearMap = MatrixOfMap.coordinateLinearMap_value A⁻¹

/-- A left inverse of a finite square matrix is also a right inverse.
Commutative rings satisfy this assertion as well as fields. -/
def left_inverse_is_right : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R),
    B * A = 1 → A * B = 1

/-- A right inverse of a finite square matrix is also a left inverse. -/
def right_inverse_is_left : Prop :=
  ∀ {R : Type*} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R),
    A * B = 1 → B * A = 1

end Specs.D05.M04.InverseMatrix
