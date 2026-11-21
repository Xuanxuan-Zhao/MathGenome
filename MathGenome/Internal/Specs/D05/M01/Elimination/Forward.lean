import MathGenome.Internal.Specs.D05.M01.Echelon
import MathGenome.Internal.Specs.D05.M01.RowOps

/-!
Forward half of K05.01.elimination, paper.tex:736–742.
The auxiliary data describe the actual pivot procedure, not a postulated
elimination certificate. Its existence and its invariants are separate targets.
-/
namespace D05.M01.Elimination

open RowOps
universe u
variable {K : Type u} [Field K] {m n : ℕ}

/-- Operations are applied in list order, including the empty list. -/
def applyOps (ops : List (RowOperation K m)) (A : Matrix (Fin m) (Fin n) K) :=
  ops.foldl (fun B op => RowOpsSpec.applyOpValue op B) A

/-- All unprocessed rows are zero in the columns before the cursor. -/
def LowerZero (A : Matrix (Fin m) (Fin n) K) (r c : ℕ) : Prop :=
  ∀ i j, r ≤ i.val → j.val < c → A i j = 0

/-- The entry formula for swapping the selected row into place, dividing by
its pivot, and subtracting the pivot-column multiple from every lower row.
The stage predicate below requires the denominator to be nonzero. -/
noncomputable def pivotMatrix (A : Matrix (Fin m) (Fin n) K)
    (r q : Fin m) (d : Fin n) : Matrix (Fin m) (Fin n) K :=
  let S : Matrix (Fin m) (Fin n) K := fun i j => A (Equiv.swap r q i) j
  let N : Matrix (Fin m) (Fin n) K :=
    fun i j => if i = r then (A q d)⁻¹ * S r j else S i j
  fun i j => if r < i then N i j - N i d * N r j else N i j

/-- One leftmost-nonzero-pivot stage. The witness operations must really
produce the displayed matrix. No echelon or preservation conclusion is a field. -/
def PivotStage (A B : Matrix (Fin m) (Fin n) K)
    (r : Fin m) (c : ℕ) (d : Fin n) : Prop :=
  c ≤ d.val ∧ ∃ q : Fin m, r ≤ q ∧ A q d ≠ 0 ∧
    (∀ i j, r ≤ i → j < d → A i j = 0) ∧
    B = pivotMatrix A r q d ∧ ∃ ops, applyOps ops A = B

/-- A complete forward run. Each step advances one row and goes past its
pivot column. Stop is allowed exactly when every remaining row is zero. -/
inductive ForwardTrace : ℕ → ℕ → Matrix (Fin m) (Fin n) K →
    List (Fin n) → Matrix (Fin m) (Fin n) K → Prop where
  | stop {r c A} (zero : ∀ i : Fin m, r ≤ i.val → A i = 0) :
      ForwardTrace r c A [] A
  | step {r c A B C d ps} (hr : r < m)
      (stage : PivotStage A B ⟨r, hr⟩ c d)
      (tail : ForwardTrace (r + 1) (d.val + 1) B ps C) :
      ForwardTrace r c A (d :: ps) C

end D05.M01.Elimination

namespace D05.M01.Elimination.ForwardSpec
open D05.M01.Elimination
universe u

/-- A pivot stage is available whenever an unprocessed entry is nonzero. -/
def pivot_stage_exists : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K)
    (r : Fin m) (c : ℕ), LowerZero A r.val c →
    (∃ i j, r ≤ i ∧ A i j ≠ 0) →
    ∃ d B, PivotStage A B r c d

/-- Old rows and all earlier columns are unchanged; the new pivot is a leading
one; the lower rows are zero through the new pivot column (including skipped columns). -/
def pivot_stage_invariants : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A B : Matrix (Fin m) (Fin n) K)
    (r : Fin m) (c : ℕ) (d : Fin n), PivotStage A B r c d →
    (∀ i, i < r → B i = A i) ∧
    (∀ i j, j.val < c → B i j = A i j) ∧
    B.IsLeadingEntry r d ∧ B r d = 1 ∧ LowerZero B (r.val + 1) (d.val + 1)

/-- Strict column progress and the row/column bounds count pivot stages,
not the number of elementary row operations. -/
def trace_bounds : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} {A B : Matrix (Fin m) (Fin n) K}
    {r c : ℕ} {ps : List (Fin n)}, ForwardTrace r c A ps B →
    r ≤ m → c ≤ n → ps.length ≤ min (m - r) (n - c) ∧
      ps.Pairwise (· < ·) ∧ ∀ d ∈ ps, c ≤ d.val

/-- Processed rows and earlier columns remain fixed throughout the rest of a run. -/
def trace_preserves : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} {A B : Matrix (Fin m) (Fin n) K}
    {r c : ℕ} {ps : List (Fin n)}, ForwardTrace r c A ps B →
    (∀ i : Fin m, i.val < r → B i = A i) ∧
      (∀ i j, j.val < c → B i j = A i j)

/-- The t-th stage really produces the final leading unit in row r+t;
exactly ps.length rows are processed, and all subsequent rows are zero. -/
def trace_pivots : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} {A B : Matrix (Fin m) (Fin n) K}
    {r c : ℕ} {ps : List (Fin n)}, ForwardTrace r c A ps B →
    (∀ t : Fin ps.length, ∃ i : Fin m, i.val = r + t.val ∧
      B.IsLeadingEntry i (ps.get t) ∧ B i (ps.get t) = 1) ∧
    (∀ i : Fin m, r + ps.length ≤ i.val → B i = 0)

/-- The original unconditional existence assertion, together with an actual
terminating forward trace and its min(m,n) bound. No positivity assumption on
m or n and no nonzero-matrix assumption is made. -/
def forward_elimination : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K),
    ∃ (ops : List (RowOps.RowOperation K m)) (B : Matrix (Fin m) (Fin n) K)
      (ps : List (Fin n)), applyOps ops A = B ∧ ForwardTrace 0 0 A ps B ∧
      ps.length ≤ min m n ∧ ps.Pairwise (· < ·) ∧ B.IsRowEchelon

/-- The zero matrix, and hence either empty shape, needs zero stages and operations. -/
def zero_trace : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ},
    ForwardTrace 0 0 (0 : Matrix (Fin m) (Fin n) K) [] 0 ∧
      applyOps ([] : List (RowOps.RowOperation K m))
        (0 : Matrix (Fin m) (Fin n) K) = 0 ∧
      (0 : Matrix (Fin m) (Fin n) K).IsRowEchelon

def empty_rows : Prop :=
  ∀ {K : Type u} [Field K] {n : ℕ} (A : Matrix (Fin 0) (Fin n) K),
    ForwardTrace 0 0 A [] A ∧ A.IsRowEchelon

def empty_columns : Prop :=
  ∀ {K : Type u} [Field K] {m : ℕ} (A : Matrix (Fin m) (Fin 0) K),
    ForwardTrace 0 0 A [] A ∧ A.IsRowEchelon

end D05.M01.Elimination.ForwardSpec
