import MathGenome.Internal.Specs.D05.M04.RankBridge
import MathGenome.Internal.Specs.D05.M05.DetDefinition

/-! Independent statements for the rank–minor lemma, paper.tex:839–846.
The rank is the dimension of the range of `A.mulVecLin` (`Matrix.rank`).
A square submatrix is selected by embeddings of its row and column positions;
thus each selected row/column occurs once. No positivity or square-shape
assumption is imposed on the original matrix, and size zero is permitted.
The determinant is the shared column-indexed Leibniz determinant.
-/

namespace Specs.D05.M05.Adjugate.RankMinors

open _root_.D05.M05

/-- Every nonzero square minor has size at most the column-map rank. -/
def minor_size_le_rank : Prop :=
  ∀ {K : Type*} [Field K] {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) K)
    (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin n),
    determinant (A.submatrix rows cols) ≠ 0 → k ≤ A.rank

/-- Some square submatrix of size equal to the rank has nonzero determinant. -/
def exists_rank_minor : Prop :=
  ∀ {K : Type*} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K),
    ∃ (rows : Fin A.rank ↪ Fin m) (cols : Fin A.rank ↪ Fin n),
      determinant (A.submatrix rows cols) ≠ 0

/-- Rank is the attained maximum of all sizes of nonzero square minors. -/
def rank_isGreatest_minor_sizes : Prop :=
  ∀ {K : Type*} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K),
    IsGreatest {k : ℕ | ∃ (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin n),
      determinant (A.submatrix rows cols) ≠ 0} A.rank

/-- Every minor larger than the rank vanishes, including positive-size minors
of a rank-zero matrix. -/
def larger_minors_vanish : Prop :=
  ∀ {K : Type*} [Field K] {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) K), A.rank < k →
    ∀ (rows : Fin k ↪ Fin m) (cols : Fin k ↪ Fin n),
      determinant (A.submatrix rows cols) = 0

/-- The empty minor has determinant one, even for an empty original shape. -/
def empty_minor : Prop :=
  ∀ {R : Type*} [CommRing R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R),
    determinant (A.submatrix (Fin.elim0 : Fin 0 → Fin m)
      (Fin.elim0 : Fin 0 → Fin n)) = 1

end Specs.D05.M05.Adjugate.RankMinors
