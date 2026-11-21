import MathGenome.Internal.Specs.D05.M14.QrCholesky.Qr
import MathGenome.Internal.Specs.D05.M14.QrCholesky.Cholesky

/-! The two factorization conclusions of K05.14.qr_cholesky,
paper.tex:2611–2626. These statements use the canonical Euclidean columns
and the paper's first-slot-linear orthonormality predicate. Natural-number
dimensions include empty matrices. Strictly positive real diagonal entries
are expressed using the real embedding into either real or complex scalars. -/

namespace Specs.D05.M14.QrCholesky

open _root_.D05.QrCholesky
open scoped ComplexOrder

/-- Full column rank gives the dimension bound and a unique reduced QR
factorization. Uniqueness ranges over all pairs of the required shapes. -/
def reduced_qr : Prop :=
  ∀ {F : Type*} [RCLike F] {m n : ℕ} (A : Matrix (Fin m) (Fin n) F),
    FullColumnRank A → n ≤ m ∧
    ∃! p : Matrix (Fin m) (Fin n) F × Matrix (Fin n) (Fin n) F,
      A = p.1 * p.2 ∧
      _root_.D05.orthonormalFamily (F := F) (columns p.1) ∧
      p.2.IsUpperTriangular ∧
      ∀ i, ∃ r : ℝ, 0 < r ∧ p.2 i i = (r : F)

/-- Positive definiteness includes Hermitian symmetry; dagger is conjugate
transpose. No positivity assumption on dimension is imposed. -/
def cholesky : Prop :=
  ∀ {F : Type*} [RCLike F] {n : ℕ} (H : Matrix (Fin n) (Fin n) F),
    H.PosDef → ∃! R : Matrix (Fin n) (Fin n) F,
      H = R.conjTranspose * R ∧ R.IsUpperTriangular ∧
      ∀ i, ∃ r : ℝ, 0 < r ∧ R i i = (r : F)

end Specs.D05.M14.QrCholesky
