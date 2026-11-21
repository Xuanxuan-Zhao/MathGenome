import MathGenome.Internal.Specs.D05.M01.System
import Mathlib.LinearAlgebra.Matrix.Echelon.Basic

/-!
Independent interface for paper.tex:733–734 (K05.01.echelon).
Rows and columns have their usual `Fin` order, including empty shapes.
The canonical predicates are Mathlib's; the equivalences below specify their
textbook meaning independently of the implementation. No elimination or
row-operation certificate is assumed.
-/
namespace D05.M01.EchelonSpec

universe u

def IsPivotType :=
  ∀ {K : Type u} [Field K] {m n : ℕ},
    Matrix (Fin m) (Fin n) K → Fin m → Fin n → Prop

def IsPivotValue : IsPivotType := fun A i c => A.IsLeadingEntry i c

def IsRowEchelonType :=
  ∀ {K : Type u} [Field K] {m n : ℕ}, Matrix (Fin m) (Fin n) K → Prop

def IsRowEchelonValue : IsRowEchelonType := fun A => A.IsRowEchelon

def IsReducedRowEchelonType :=
  ∀ {K : Type u} [Field K] {m n : ℕ}, Matrix (Fin m) (Fin n) K → Prop

def IsReducedRowEchelonValue : IsReducedRowEchelonType :=
  fun A => A.IsReducedRowEchelon

/-- A pivot is exactly the first nonzero entry of its row. -/
def pivot_iff : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) i c,
    IsPivotValue A i c ↔ (∀ j, j < c → A i j = 0) ∧ A i c ≠ 0

/-- Every nonzero row has a pivot; zero rows have none. -/
def exists_pivot_iff : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) i,
    (∃ c, IsPivotValue A i c) ↔ A i ≠ 0

def pivot_unique : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) i c d,
    IsPivotValue A i c → IsPivotValue A i d → c = d

/-- Zero rows are at the bottom and the leading positions strictly increase.
The all-pairs condition is equivalent to the consecutive-row version below. -/
def rowEchelon_iff : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K),
    IsRowEchelonValue A ↔
      (∀ i k, i < k → A i = 0 → A k = 0) ∧
      (∀ i k c d, i < k → IsPivotValue A i c → IsPivotValue A k d → c < d)

/-- The paper's literal consecutive-nonzero-row convention, with zero rows last. -/
def rowEchelon_iff_consecutive : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K),
    IsRowEchelonValue A ↔
      (∀ i k, i < k → A i = 0 → A k = 0) ∧
      (∀ i k c d, k.val = i.val + 1 →
        IsPivotValue A i c → IsPivotValue A k d → c < d)

/-- Entries below any pivot vanish, without normalizing its value. -/
def below_pivot_zero : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K),
    IsRowEchelonValue A → ∀ i k c, i < k → IsPivotValue A i c → A k c = 0

/-- Reduced means echelon, with unit pivots and no other nonzero entry in a pivot column. -/
def reducedRowEchelon_iff : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K),
    IsReducedRowEchelonValue A ↔ IsRowEchelonValue A ∧
      ∀ i c, IsPivotValue A i c → A i c = 1 ∧ ∀ k, k ≠ i → A k c = 0

def reduced_isRowEchelon : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K),
    IsReducedRowEchelonValue A → IsRowEchelonValue A

/-- Includes all-zero matrices of arbitrary rectangular shape. -/
def zero_forms : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ},
    IsRowEchelonValue (0 : Matrix (Fin m) (Fin n) K) ∧
    IsReducedRowEchelonValue (0 : Matrix (Fin m) (Fin n) K)

/-- The empty shapes require no nonemptiness hypothesis. -/
def empty_rows_forms : Prop :=
  ∀ {K : Type u} [Field K] {n : ℕ} (A : Matrix (Fin 0) (Fin n) K),
    IsRowEchelonValue A ∧ IsReducedRowEchelonValue A

def empty_columns_forms : Prop :=
  ∀ {K : Type u} [Field K] {m : ℕ} (A : Matrix (Fin m) (Fin 0) K),
    IsRowEchelonValue A ∧ IsReducedRowEchelonValue A

/-- Augmentation uses all n+1 columns, including the final right-hand side. -/
def augmented_pivot_last_iff : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) i,
    IsPivotValue (SystemSpec.augmentedMatrixValue A b) i (Fin.last n) ↔
      A i = 0 ∧ b i ≠ 0

/-- A last-column pivot is a contradiction row in the underlying system.
No elimination-existence theorem is needed for this implication. -/
def last_pivot_no_solution : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) i,
    IsPivotValue (SystemSpec.augmentedMatrixValue A b) i (Fin.last n) →
      ¬ ∃ x, SystemSpec.IsSolutionValue A b x

end D05.M01.EchelonSpec
