import MathGenome.Internal.Specs.D05.M01.Echelon
import MathGenome.Internal.Specs.D05.M01.RowOps
import MathGenome.Internal.Specs.D05.M02.Span

/-!
Independent interface for the row-space stage of K05.01.rref_unique,
paper.tex:744–752. All shapes use ordered `Fin` indices, including empty shapes.
The span is the canonical algebraic span of the rows, not a certificate supplied
by an elimination procedure. Expected results below are full proposition types.
-/
namespace Specs.D05.M01.RrefUnique.RowSpace

universe u

def rowSpace_type := ∀ {K : Type u} [Field K] {m n : ℕ},
  Matrix (Fin m) (Fin n) K → Submodule K (Fin n → K)

def rowSpace_value : rowSpace_type := fun A => Submodule.span _ (Set.range A)

/-- Intrinsic leading columns of nonzero vectors are exactly the pivot columns. -/
def leading_columns_iff : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (R : Matrix (Fin m) (Fin n) K),
    D05.M01.EchelonSpec.IsReducedRowEchelonValue R → ∀ c : Fin n,
    (∃ x ∈ rowSpace_value R, (∀ j, j < c → x j = 0) ∧ x c ≠ 0) ↔
      ∃ i, D05.M01.EchelonSpec.IsPivotValue R i c

/-- Pivot-coordinate evaluations jointly detect zero in the entire row span. -/
def zero_of_pivot_coordinates : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (R : Matrix (Fin m) (Fin n) K),
    D05.M01.EchelonSpec.IsReducedRowEchelonValue R →
    ∀ x ∈ rowSpace_value R,
    (∀ i c, D05.M01.EchelonSpec.IsPivotValue R i c → x c = 0) → x = 0

/-- Equal row spans determine the same pivot column at every ordered row. -/
def ordered_pivots_iff : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (R S : Matrix (Fin m) (Fin n) K),
    D05.M01.EchelonSpec.IsReducedRowEchelonValue R →
    D05.M01.EchelonSpec.IsReducedRowEchelonValue S →
    rowSpace_value R = rowSpace_value S →
    ∀ i c, D05.M01.EchelonSpec.IsPivotValue R i c ↔
      D05.M01.EchelonSpec.IsPivotValue S i c

/-- The uniqueness statement uses only reducedness and equality of row spans. -/
def eq_of_rowSpace_eq : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (R S : Matrix (Fin m) (Fin n) K),
    D05.M01.EchelonSpec.IsReducedRowEchelonValue R →
    D05.M01.EchelonSpec.IsReducedRowEchelonValue S →
    rowSpace_value R = rowSpace_value S → R = S

/-- Every permitted elementary operation preserves row span, without reducedness. -/
def row_operation_preserves_rowSpace : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ}
    (op : D05.M01.RowOps.RowOperation K m) (A : Matrix (Fin m) (Fin n) K),
    rowSpace_value (D05.M01.RowOpsSpec.applyOpValue op A) = rowSpace_value A

end Specs.D05.M01.RrefUnique.RowSpace
