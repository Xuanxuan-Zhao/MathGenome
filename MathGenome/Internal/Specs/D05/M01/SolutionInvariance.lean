import MathGenome.Internal.Specs.D05.M01.RowOps

/-!
Independent statements for paper.tex:725–731, K05.01.solution_invariance.
All row operations use the shared permitted-operation data. The solution
predicate and augmentation use the upstream expected values, not candidate
implementations. Sizes may be zero. Lists act in their written order.
-/
namespace D05.M01.SolutionInvarianceSpec

open D05.M01.RowOps
open scoped Matrix
universe u

/-- The elementary-matrix formulation, in both directions. -/
def elementary_solution_iff : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (op : RowOperation K m)
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (x : Fin n → K),
    SystemSpec.IsSolutionValue (RowOpsSpec.elementaryMatrixValue op * A)
      (RowOpsSpec.elementaryMatrixValue op *ᵥ b) x ↔
      SystemSpec.IsSolutionValue A b x

/-- Acting on the entire augmentation acts on its coefficient and last columns. -/
def applyOp_augmented : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (op : RowOperation K m)
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K),
    RowOpsSpec.applyOpValue op (SystemSpec.augmentedMatrixValue A b) =
      SystemSpec.augmentedMatrixValue (RowOpsSpec.applyOpValue op A)
        (RowOpsSpec.elementaryMatrixValue op *ᵥ b)

/-- The coefficient matrix and right-hand side undergo the same operation. -/
def row_operation_solution_iff : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (op : RowOperation K m)
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (x : Fin n → K),
    SystemSpec.IsSolutionValue (RowOpsSpec.applyOpValue op A)
      (RowOpsSpec.elementaryMatrixValue op *ᵥ b) x ↔
      SystemSpec.IsSolutionValue A b x

/-- A direct statement on all columns of an arbitrary augmented matrix. -/
def augmented_solution_iff : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (op : RowOperation K m)
    (M : Matrix (Fin m) (Fin (n + 1)) K) (x : Fin n → K),
    SystemSpec.IsSolutionValue
      (fun i j => RowOpsSpec.applyOpValue op M i j.castSucc)
      (fun i => RowOpsSpec.applyOpValue op M i (Fin.last n)) x ↔
    SystemSpec.IsSolutionValue (fun i j => M i j.castSucc)
      (fun i => M i (Fin.last n)) x

def applySequenceType :=
  ∀ {K : Type u} [Field K] {m p : ℕ},
    List (RowOperation K m) → Matrix (Fin m) (Fin p) K → Matrix (Fin m) (Fin p) K

/-- The first listed operation is performed first; the empty list does nothing. -/
def applySequenceValue : applySequenceType :=
  fun ops M => ops.foldl (fun N op => RowOpsSpec.applyOpValue op N) M

/-- Every finite sequence preserves every solution, with no consistency premise. -/
def sequence_solution_iff : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (ops : List (RowOperation K m))
    (M : Matrix (Fin m) (Fin (n + 1)) K) (x : Fin n → K),
    SystemSpec.IsSolutionValue
      (fun i j => applySequenceValue ops M i j.castSucc)
      (fun i => applySequenceValue ops M i (Fin.last n)) x ↔
    SystemSpec.IsSolutionValue (fun i j => M i j.castSucc)
      (fun i => M i (Fin.last n)) x

/-- In particular, reducing `[A | b]` preserves exactly the original solutions. -/
def sequence_preserves_solutions : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (ops : List (RowOperation K m))
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (x : Fin n → K),
    SystemSpec.IsSolutionValue
      (fun i j => applySequenceValue ops (SystemSpec.augmentedMatrixValue A b) i j.castSucc)
      (fun i => applySequenceValue ops (SystemSpec.augmentedMatrixValue A b) i (Fin.last n)) x ↔
    SystemSpec.IsSolutionValue A b x

end D05.M01.SolutionInvarianceSpec
