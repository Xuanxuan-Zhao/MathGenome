import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
Independent statements for the triangular-matrix stage of K05.14.qr_cholesky,
paper.tex:2611–2626. Coordinates are columns. Over `RCLike F`, `Cᴴ * C = 1`
is the unitary (orthogonal when F = ℝ) criterion; it is a one-sided inverse
identity for a square matrix and hence also gives `C * Cᴴ = 1`.
Positive real entries are expressed by equality to a strictly positive real
scalar. All sizes are natural numbers, including zero. The inverse statements
hold over any field, and require no positive size or chosen inverse certificate.
-/

noncomputable section

namespace Specs.D05.M14.QrCholesky.TriangularUnitary

/-- The one-sided adjoint criterion used below is precisely membership in the
canonical matrix unitary group, including its real orthogonal specialization. -/
def unitary_criterion : Prop :=
  ∀ {F : Type*} [RCLike F] {n : ℕ} (C : Matrix (Fin n) (Fin n) F),
    C ∈ Matrix.unitaryGroup (Fin n) F ↔ C.conjTranspose * C = 1

/-- An invertible upper triangular matrix has upper triangular inverse.
The diagonal need not be separately assumed nonzero. -/
def upper_triangular_inverse : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
    A.IsUpperTriangular → IsUnit A → A⁻¹.IsUpperTriangular

/-- Nonzero diagonal already suffices for invertibility and an upper triangular
inverse; the two products verify that the nonsingular inverse is an actual inverse. -/
def nonzero_diagonal_inverse : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
    A.IsUpperTriangular → (∀ i, A i i ≠ 0) →
      IsUnit A ∧ A⁻¹.IsUpperTriangular ∧ A⁻¹ * A = 1 ∧ A * A⁻¹ = 1

/-- An upper triangular real/complex unitary matrix is diagonal and its
individual diagonal entries have modulus one. -/
def upper_triangular_unitary : Prop :=
  ∀ {F : Type*} [RCLike F] {n : ℕ} (C : Matrix (Fin n) (Fin n) F),
    C.IsUpperTriangular → C.conjTranspose * C = 1 →
      C = Matrix.diagonal (fun i => C i i) ∧ ∀ i, ‖C i i‖ = 1

/-- Positive real diagonal removes every phase (or real sign). -/
def positive_diagonal_unitary : Prop :=
  ∀ {F : Type*} [RCLike F] {n : ℕ} (C : Matrix (Fin n) (Fin n) F),
    C.IsUpperTriangular → C.conjTranspose * C = 1 →
      (∀ i, ∃ r : ℝ, 0 < r ∧ C i i = (r : F)) → C = 1

/-- Explicit empty-size boundary for the matrix claims. -/
def empty_matrix : Prop :=
  ∀ {F : Type*} [RCLike F] (C : Matrix (Fin 0) (Fin 0) F),
    C = 1 ∧ C.IsUpperTriangular ∧ C.conjTranspose * C = 1 ∧
      C⁻¹.IsUpperTriangular

end Specs.D05.M14.QrCholesky.TriangularUnitary
