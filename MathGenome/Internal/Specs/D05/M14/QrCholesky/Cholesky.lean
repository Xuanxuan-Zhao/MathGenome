import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Cholesky factorization, paper.tex:2611–2626. Matrices act on coordinate
columns, so dagger is conjugate transpose, over both real and complex scalars.
`Matrix.PosDef` includes Hermitian symmetry and strict positivity on nonzero
vectors. All sizes are natural numbers, including zero. -/

open scoped ComplexOrder

namespace Specs.D05.M14.QrCholesky.Cholesky

/-- The positive square root used for square QR is genuinely invertible. -/
def invertible_positive_root : Prop :=
  ∀ {F : Type*} [RCLike F] {n : ℕ} (H : Matrix (Fin n) (Fin n) F),
    H.PosDef → ∃ S : Matrix (Fin n) (Fin n) F,
      S.PosSemidef ∧ IsUnit S ∧ S * S = H

/-- Square QR of the positive root gives the required Cholesky factor. -/
def existence : Prop :=
  ∀ {F : Type*} [RCLike F] {n : ℕ} (H : Matrix (Fin n) (Fin n) F),
    H.PosDef → ∃ R : Matrix (Fin n) (Fin n) F,
      H = R.conjTranspose * R ∧ R.IsUpperTriangular ∧
        ∀ i, ∃ r : ℝ, 0 < r ∧ R i i = (r : F)

/-- Uniqueness quantifies over any two upper triangular positive-diagonal
factors of the same matrix. No factor or decomposition is assumed for existence. -/
def uniqueness : Prop :=
  ∀ {F : Type*} [RCLike F] {n : ℕ}
    (H R₁ R₂ : Matrix (Fin n) (Fin n) F),
    (H = R₁.conjTranspose * R₁ ∧ R₁.IsUpperTriangular ∧
      ∀ i, ∃ r : ℝ, 0 < r ∧ R₁ i i = (r : F)) →
    (H = R₂.conjTranspose * R₂ ∧ R₂.IsUpperTriangular ∧
      ∀ i, ∃ r : ℝ, 0 < r ∧ R₂ i i = (r : F)) → R₁ = R₂

/-- The full source conclusion, with uniqueness among all eligible factors. -/
def exists_unique_cholesky : Prop :=
  ∀ {F : Type*} [RCLike F] {n : ℕ} (H : Matrix (Fin n) (Fin n) F),
    H.PosDef → ∃! R : Matrix (Fin n) (Fin n) F,
      H = R.conjTranspose * R ∧ R.IsUpperTriangular ∧
        ∀ i, ∃ r : ℝ, 0 < r ∧ R i i = (r : F)

/-- The empty Hermitian matrix is positive definite vacuously and its unique
Cholesky factor is the empty identity. -/
def zero_dimension : Prop :=
  ∀ {F : Type*} [RCLike F] (H : Matrix (Fin 0) (Fin 0) F),
    H.PosDef ∧ H = (1 : Matrix (Fin 0) (Fin 0) F).conjTranspose * 1 ∧
      (1 : Matrix (Fin 0) (Fin 0) F).IsUpperTriangular ∧
      (∀ i : Fin 0, ∃ r : ℝ, 0 < r ∧ (1 : Matrix (Fin 0) (Fin 0) F) i i = (r : F)) ∧
      ∀ R : Matrix (Fin 0) (Fin 0) F, R = 1

end Specs.D05.M14.QrCholesky.Cholesky
