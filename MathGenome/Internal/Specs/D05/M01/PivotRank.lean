import MathGenome.Internal.Specs.D05.M01.Echelon
import MathGenome.Internal.Specs.D05.M01.RowOps
import MathGenome.Internal.Specs.D05.M04.RankBridge
import MathGenome.Internal.Specs.D05.M02.Basis

/-! Independent statements for K05.01.pivot_rank, paper.tex:770–776.
The pivot rows are exactly the nonzero rows. Their leading columns are chosen
from the actual entries, with no rank, independence, or spanning certificate.
An echelon form of `A` is expressed as `R = E * A` for an invertible `E`.
A separate statement supplies this relation for every finite row-operation list.
All shapes, including empty ones, are allowed. -/
namespace D05.M01.PivotRankData

universe u
variable {K : Type u} [Field K] {m n : ℕ}

/-- One index for each actual coefficient pivot, indexed by its nonzero row. -/
abbrev PivotRow (R : Matrix (Fin m) (Fin n) K) := {i : Fin m // R i ≠ 0}

/-- The leading column of a nonzero row, defined from the entries alone. -/
noncomputable def pivotColumn (R : Matrix (Fin m) (Fin n) K) (i : PivotRow R) : Fin n :=
  Classical.choose (Matrix.row_ne_zero_iff_exists_isLeadingEntry.mp i.property)

/-- Number of pivots; its agreement with the set of pivot columns is proved below. -/
noncomputable def pivotCount (R : Matrix (Fin m) (Fin n) K) : ℕ := Nat.card (PivotRow R)

end D05.M01.PivotRankData

namespace Specs.D05.M01.PivotRank
open D05.M01.PivotRankData
universe u

def pivotColumn_isLeadingEntry : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (R : Matrix (Fin m) (Fin n) K)
    (i : PivotRow R), R.IsLeadingEntry i.val (pivotColumn R i)

/-- Every leading entry is represented, and the choice of its column is unique. -/
def pivotColumn_eq_iff : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (R : Matrix (Fin m) (Fin n) K)
    (i : PivotRow R) (c : Fin n),
    pivotColumn R i = c ↔ R.IsLeadingEntry i.val c

def pivot_columns_count : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (R : Matrix (Fin m) (Fin n) K),
    R.IsRowEchelon →
    Nat.card {c : Fin n // ∃ i, R.IsLeadingEntry i c} = pivotCount R

def echelon_rank : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (R : Matrix (Fin m) (Fin n) K),
    R.IsRowEchelon → R.rank = pivotCount R

def echelon_row_column_rank : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (R : Matrix (Fin m) (Fin n) K),
    R.IsRowEchelon →
    pivotCount R = Module.finrank K (Submodule.span K (Set.range R.row)) ∧
    pivotCount R = Module.finrank K (Submodule.span K (Set.range R.col))

def pivot_columns_independent : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (R : Matrix (Fin m) (Fin n) K),
    R.IsRowEchelon → LinearIndependent K (fun i : PivotRow R => R.col (pivotColumn R i))

def pivot_columns_span : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (R : Matrix (Fin m) (Fin n) K),
    R.IsRowEchelon →
    Submodule.span K (Set.range (fun i : PivotRow R => R.col (pivotColumn R i))) =
      Submodule.span K (Set.range R.col)

/-- Ranks are those of the original matrix, not just of its altered entries. -/
def original_rank : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A R : Matrix (Fin m) (Fin n) K)
    (E : Matrix (Fin m) (Fin m) K), IsUnit E → R = E * A → R.IsRowEchelon →
    pivotCount R = Module.finrank K (Submodule.span K (Set.range A.row)) ∧
    pivotCount R = Module.finrank K (Submodule.span K (Set.range A.col))

/-- The vectors of the resulting basis are precisely the original pivot columns.
Only echelon form is required; reduced form is included as a special case. -/
def original_pivot_columns_basis : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A R : Matrix (Fin m) (Fin n) K)
    (E : Matrix (Fin m) (Fin m) K), IsUnit E → R = E * A → R.IsRowEchelon →
    ∃ b : Module.Basis (PivotRow R) K (Submodule.span K (Set.range A.col)),
      ∀ i, (b i : Fin m → K) = A.col (pivotColumn R i)

/-- Every permitted finite sequence has an invertible accumulated left multiplier.
This is not elimination existence, which belongs to its own goal. -/
def row_operations_multiplier : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ}
    (ops : List (D05.M01.RowOps.RowOperation K m)) (A : Matrix (Fin m) (Fin n) K),
    ∃ E : Matrix (Fin m) (Fin m) K, IsUnit E ∧
      ops.foldl (fun B op => D05.M01.RowOpsSpec.applyOpValue op B) A = E * A

/-- The complete conclusion directly for an echelon form obtained by any finite
sequence of the paper's permitted elementary row operations. -/
def pivots_and_original_columns : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ}
    (ops : List (D05.M01.RowOps.RowOperation K m)) (A : Matrix (Fin m) (Fin n) K),
    let R := ops.foldl (fun B op => D05.M01.RowOpsSpec.applyOpValue op B) A
    R.IsRowEchelon →
      pivotCount R = Module.finrank K (Submodule.span K (Set.range A.row)) ∧
      pivotCount R = Module.finrank K (Submodule.span K (Set.range A.col)) ∧
      ∃ b : Module.Basis (PivotRow R) K (Submodule.span K (Set.range A.col)),
        ∀ i, (b i : Fin m → K) = A.col (pivotColumn R i)

end Specs.D05.M01.PivotRank
