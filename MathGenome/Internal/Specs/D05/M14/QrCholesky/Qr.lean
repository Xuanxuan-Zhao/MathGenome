import MathGenome.Internal.Specs.D05.M12.GramSchmidt
import MathGenome.Internal.Specs.D05.M14.QrCholesky.TriangularUnitary
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Reduced QR, paper.tex:2611–2626. All shapes, including n = 0, are
allowed. Full column rank means independence of the actual indexed columns,
not a supplied factorization. The adjoint is conjugate transpose. -/
noncomputable section

namespace D05.QrCholesky

variable {F : Type*} [RCLike F] {m n : ℕ}

/-- A matrix column in the standard Euclidean inner-product space. -/
def columns (A : Matrix (Fin m) (Fin n) F) (j : Fin n) : EuclideanSpace F (Fin m) :=
  WithLp.toLp 2 (fun i => A i j)

/-- The full-column-rank condition, also for rectangular matrices. -/
def FullColumnRank (A : Matrix (Fin m) (Fin n) F) : Prop :=
  LinearIndependent F (columns A)

/-- The reduced factorization, with strictly positive real diagonal. -/
def ReducedQR (A Q : Matrix (Fin m) (Fin n) F) (R : Matrix (Fin n) (Fin n) F) : Prop :=
  A = Q * R ∧ Q.conjTranspose * Q = 1 ∧ R.IsUpperTriangular ∧
    ∀ i, ∃ r : ℝ, 0 < r ∧ R i i = (r : F)

/-- Actual normalized Gram–Schmidt columns, rather than an existence choice. -/
def gramSchmidtQ (A : Matrix (Fin m) (Fin n) F) : Matrix (Fin m) (Fin n) F :=
  fun i j => gramSchmidtVectors (F := F) (columns A) j i

/-- The residual norms give the diagonal, and first-slot-linear Fourier
coefficients give the strictly upper part. -/
def gramSchmidtR (A : Matrix (Fin m) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  fun i j => if i < j then
    firstInner (F := F) (columns A j) (gramSchmidtVectors (F := F) (columns A) i)
  else if i = j then (‖gramSchmidtResidual (F := F) (columns A) j‖ : F) else 0

end D05.QrCholesky

namespace Specs.D05.M14.QrCholesky.Qr
open _root_.D05.QrCholesky

/-- Independence of n columns in F^m forces n ≤ m. -/
def dimension_bound : Prop :=
  ∀ {F : Type*} [RCLike F] {m n : ℕ} (A : Matrix (Fin m) (Fin n) F),
    FullColumnRank A → n ≤ m

/-- The rectangular adjoint identity says exactly that the columns are
orthonormal in the paper's convention. -/
def orthonormal_columns_iff : Prop :=
  ∀ {F : Type*} [RCLike F] {m n : ℕ} (Q : Matrix (Fin m) (Fin n) F),
    _root_.D05.orthonormalFamily (F := F) (columns Q) ↔ Q.conjTranspose * Q = 1

/-- Gram–Schmidt constructs the reduced factors and preserves every initial
column span, including the empty and full initial spans. -/
def gram_schmidt_factorization : Prop :=
  ∀ {F : Type*} [RCLike F] {m n : ℕ} (A : Matrix (Fin m) (Fin n) F),
    FullColumnRank A →
    ReducedQR A (gramSchmidtQ A) (gramSchmidtR A) ∧
    ∀ k : ℕ, k ≤ n →
      Submodule.span F (columns (gramSchmidtQ A) '' {i | i.val < k}) =
        Submodule.span F (columns A '' {i | i.val < k})

/-- The transition through the common column space, not a square-Q inverse.
It is unitary, upper triangular, and has positive real diagonal. -/
def common_column_transition : Prop :=
  ∀ {F : Type*} [RCLike F] {m n : ℕ}
    (A Q Q' : Matrix (Fin m) (Fin n) F) (R R' : Matrix (Fin n) (Fin n) F),
    ReducedQR A Q R → ReducedQR A Q' R' →
    Submodule.span F (Set.range (columns Q)) =
      Submodule.span F (Set.range (columns A)) ∧
    Submodule.span F (Set.range (columns Q')) =
      Submodule.span F (Set.range (columns A)) ∧
    let C := Q.conjTranspose * Q'
    Q' = Q * C ∧ C.conjTranspose * C = 1 ∧ R = C * R' ∧
      C.IsUpperTriangular ∧ ∀ i, ∃ r : ℝ, 0 < r ∧ C i i = (r : F)

def uniqueness : Prop :=
  ∀ {F : Type*} [RCLike F] {m n : ℕ}
    (A Q Q' : Matrix (Fin m) (Fin n) F) (R R' : Matrix (Fin n) (Fin n) F),
    ReducedQR A Q R → ReducedQR A Q' R' → Q = Q' ∧ R = R'

/-- The full existence-and-uniqueness conclusion quantifies over all pairs. -/
def exists_unique_reduced_qr : Prop :=
  ∀ {F : Type*} [RCLike F] {m n : ℕ} (A : Matrix (Fin m) (Fin n) F),
    FullColumnRank A →
    ∃! p : Matrix (Fin m) (Fin n) F × Matrix (Fin n) (Fin n) F,
      ReducedQR A p.1 p.2

/-- Empty columns require neither positive m nor a normalization step. -/
def zero_columns : Prop :=
  ∀ {F : Type*} [RCLike F] {m : ℕ} (A : Matrix (Fin m) (Fin 0) F),
    FullColumnRank A ∧ ReducedQR A (gramSchmidtQ A) (gramSchmidtR A) ∧
      ∀ (Q : Matrix (Fin m) (Fin 0) F) (R : Matrix (Fin 0) (Fin 0) F),
        Q = gramSchmidtQ A ∧ R = gramSchmidtR A

end Specs.D05.M14.QrCholesky.Qr
