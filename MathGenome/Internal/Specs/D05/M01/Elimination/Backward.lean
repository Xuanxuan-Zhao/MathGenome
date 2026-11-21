import MathGenome.Internal.Specs.D05.M01.Echelon
import MathGenome.Internal.Specs.D05.M01.RowOps

/-! Independent statement of the backward stage in paper.tex:736–742.
The list consists of the shared, genuine elementary operations. No assumption on
positive matrix sizes, pivot count, or preexisting normalization is made. -/
namespace D05.M01.Elimination

universe u

/-- Execute a finite list in chronological order, on every column. -/
def applyOperations {K : Type u} [Field K] {m n : ℕ}
    (ops : List (RowOps.RowOperation K m)) (A : Matrix (Fin m) (Fin n) K) :
    Matrix (Fin m) (Fin n) K :=
  ops.foldl (fun B op => RowOpsSpec.applyOpValue op B) A

end D05.M01.Elimination

namespace D05.M01.Elimination.BackwardSpec

universe u

/-- Every echelon matrix admits a finite backward reduction with exactly its
original pivot positions, including the empty and no-pivot cases. -/
def exists_reduced_same_pivots : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K),
    A.IsRowEchelon → ∃ ops : List (RowOps.RowOperation K m),
      (applyOperations ops A).IsReducedRowEchelon ∧
      ∀ i c, (applyOperations ops A).IsLeadingEntry i c ↔ A.IsLeadingEntry i c

/-- With no pivots the empty list already gives reduced form. -/
def no_pivots_reduced : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K),
    (∀ i c, ¬ A.IsLeadingEntry i c) → (applyOperations [] A).IsReducedRowEchelon

/-- No operation is needed when the row index set is empty. -/
def empty_rows_reduced : Prop :=
  ∀ {K : Type u} [Field K] {n : ℕ} (A : Matrix (Fin 0) (Fin n) K),
    (applyOperations [] A).IsReducedRowEchelon

/-- No operation is needed when the column index set is empty. -/
def empty_columns_reduced : Prop :=
  ∀ {K : Type u} [Field K] {m : ℕ} (A : Matrix (Fin m) (Fin 0) K),
    (applyOperations [] A).IsReducedRowEchelon

end D05.M01.Elimination.BackwardSpec
