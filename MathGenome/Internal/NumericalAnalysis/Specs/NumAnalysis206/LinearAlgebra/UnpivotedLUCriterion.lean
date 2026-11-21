import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.PivotedLU
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! W20: sequential elimination without exchanges or skipped columns.
The completed first row and first column are removed at each stage. The
remaining entries are exactly the ordinary row-subtraction Schur update.
A division is required in every column except the last, even if the entries
below that pivot happen to vanish. -/
noncomputable section
namespace NumAnalysis206.UnpivotedLU
open NumAnalysis206.MatrixDefinitions
universe u
variable {K : Type u} [Field K]

/-- The active block after dividing by the first pivot and subtracting the
multipliers times the first row. Only used for a successful step when A₀₀ ≠ 0. -/
def schur {n : ℕ} (A : Mat K (n + 1) (n + 1)) : Mat K n n :=
  fun i j => A i.succ j.succ - (A i.succ 0 / A 0 0) * A 0 j.succ

/-- Success of the attempted algorithm. A zero division pivot stops the run;
there is no row exchange or column skip. The last diagonal needs no division. -/
def Succeeds : {n : ℕ} → Mat K n n → Prop
  | 0, _ => True
  | 1, _ => True
  | _n + 2, A => A 0 0 ≠ 0 ∧ Succeeds (schur A)

/-- Last diagonal produced by the same successive updates. This has a
mathematical algorithmic meaning under `Succeeds`; it is never defined for
an empty matrix. -/
def terminal : {n : ℕ} → Mat K (n + 1) (n + 1) → K
  | 0, A => A 0 0
  | _n + 1, A => terminal (schur A)

/-- The determinant of the actual leading k by k principal submatrix. -/
def leadingMinor {n : ℕ} (A : Mat K n n) (k : ℕ) (hk : k ≤ n) : K :=
  (A.submatrix (Fin.castLE hk) (Fin.castLE hk)).det

def exchange : Mat K 2 2 := !![0, 1; 1, 0]
def zeroOneDiagonal : Mat K 2 2 := !![0, 0; 0, 1]
end NumAnalysis206.UnpivotedLU

namespace Specs.NumAnalysis206.UnpivotedLU
open _root_.NumAnalysis206.MatrixDefinitions _root_.NumAnalysis206.UnpivotedLU
universe u

/-- Both directions include all square matrices over every field. -/
def criterion : Prop :=
  ∀ {K : Type u} [Field K] {n : ℕ} (A : Mat K n n),
    Succeeds A ↔ ∀ k, 0 < k → (hk : k < n) → leadingMinor A k hk.le ≠ 0

/-- The terminal claim is conditional only on earlier division steps succeeding. -/
def terminal_criterion : Prop :=
  ∀ {K : Type u} [Field K] {n : ℕ} (A : Mat K (n + 1) (n + 1)),
    Succeeds A → (terminal A ≠ 0 ↔ A.det ≠ 0)

/-- Empty and singleton matrices have no required division pivots. The empty
matrix is outside the domain of `terminal`. -/
def boundary_cases : Prop :=
  ∀ {K : Type u} [Field K],
    (∀ A : Mat K 0 0, Succeeds A ∧ A.det = 1) ∧
    (∀ A : Mat K 1 1, Succeeds A ∧ terminal A = A 0 0)

/-- Invertibility alone does not permit the first unpivoted division. -/
def exchange_example : Prop :=
  ∀ {K : Type u} [Field K],
    IsUnit (exchange (K := K)) ∧
    leadingMinor (exchange (K := K)) 1 (by decide) = 0 ∧
    ¬ Succeeds (exchange (K := K))

/-- A bare LU decomposition does not assert algorithmic success. -/
def bare_lu_example : Prop :=
  ∀ {K : Type u} [Field K],
    IsUnitLowerTriangular (1 : Mat K 2 2) ∧
    IsUpperTriangular (zeroOneDiagonal (K := K)) ∧
    (1 : Mat K 2 2) * zeroOneDiagonal = zeroOneDiagonal ∧
    ¬ Succeeds (zeroOneDiagonal (K := K))

/-- The active-block update is the upstream exact row-elimination operation,
with the selected row equal to the pivot row (so no exchange). -/
def schur_matches_eliminate : Prop :=
  ∀ {K : Type u} [Field K] {n : ℕ} (A : Mat K (n + 1) (n + 1)) (i j : Fin n),
    schur A i j = _root_.NumAnalysis206.PivotedLU.eliminate A 0 0 0 i.succ j.succ
end Specs.NumAnalysis206.UnpivotedLU
