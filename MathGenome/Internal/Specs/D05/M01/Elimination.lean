import MathGenome.Internal.Specs.D05.M01.Elimination.Forward
import MathGenome.Internal.Specs.D05.M01.Elimination.Backward

/-!
Independent statements for K05.01.elimination, paper.tex:736–742.
The operation type enforces distinct rows for swaps/additions and nonzero
scalars for rescaling. The shared `applyOps` executes a finite list in order.
All matrix shapes, including either zero dimension, are quantified below.
No elimination result is assumed by these proposition definitions.
-/
namespace D05.M01.EliminationSpec

open D05.M01.Elimination D05.M01.RowOps
universe u

/-- Gaussian elimination followed by Gauss–Jordan elimination, with the
actual operation lists, intermediate and final forms, and the terminating
forward trace. The bound counts pivot stages, not individual row operations.
Backward reduction preserves the forward pivot positions. -/
def gaussian_gaussJordan : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K),
    ∃ (forward backward : List (RowOperation K m))
      (B R : Matrix (Fin m) (Fin n) K) (ps : List (Fin n)),
      applyOps forward A = B ∧ B.IsRowEchelon ∧
      ForwardTrace 0 0 A ps B ∧ ps.length ≤ min m n ∧ ps.Pairwise (· < ·) ∧
      applyOps backward B = R ∧ R.IsReducedRowEchelon ∧
      (∀ i c, R.IsLeadingEntry i c ↔ B.IsLeadingEntry i c) ∧
      applyOps (forward ++ backward) A = R

/-- The unconditional Gaussian existence statement. -/
def exists_echelon : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K),
    ∃ ops : List (RowOperation K m), (applyOps ops A).IsRowEchelon

/-- The unconditional Gauss–Jordan existence statement. -/
def exists_reduced : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K),
    ∃ ops : List (RowOperation K m), (applyOps ops A).IsReducedRowEchelon

/-- A zero matrix already has both forms and requires no operations. -/
def zero_reduction : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ},
    applyOps ([] : List (RowOperation K m)) (0 : Matrix (Fin m) (Fin n) K) = 0 ∧
    (0 : Matrix (Fin m) (Fin n) K).IsRowEchelon ∧
    (0 : Matrix (Fin m) (Fin n) K).IsReducedRowEchelon

def empty_rows_reduction : Prop :=
  ∀ {K : Type u} [Field K] {n : ℕ} (A : Matrix (Fin 0) (Fin n) K),
    applyOps ([] : List (RowOperation K 0)) A = A ∧
    A.IsRowEchelon ∧ A.IsReducedRowEchelon

def empty_columns_reduction : Prop :=
  ∀ {K : Type u} [Field K] {m : ℕ} (A : Matrix (Fin m) (Fin 0) K),
    applyOps ([] : List (RowOperation K m)) A = A ∧
    A.IsRowEchelon ∧ A.IsReducedRowEchelon

end D05.M01.EliminationSpec
