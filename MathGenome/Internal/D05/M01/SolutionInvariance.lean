import MathGenome.Internal.Specs.D05.M01.SolutionInvariance
import MathGenome.Internal.D05.M01.RowOps

/-! Preservation of the full solution set, paper.tex:725–731. -/
namespace D05.M01.SolutionInvariance

open D05.M01.RowOps
open scoped Matrix BigOperators
universe u

/-- Cancel an elementary matrix by its displayed inverse, without assuming a solution. -/
theorem elementary_solution_iff {K : Type u} [Field K] {m n : ℕ}
    (op : RowOperation K m) (A : Matrix (Fin m) (Fin n) K)
    (b : Fin m → K) (x : Fin n → K) :
    System.IsSolution (elementaryMatrix op * A) (elementaryMatrix op *ᵥ b) x ↔
      System.IsSolution A b x := by
  change (elementaryMatrix op * A) *ᵥ x = elementaryMatrix op *ᵥ b ↔ A *ᵥ x = b
  rw [← Matrix.mulVec_mulVec]
  constructor
  · intro h
    have h' := congrArg (fun v => elementaryMatrix (inverse op) *ᵥ v) h
    simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, elementary_inverse_mul,
      Matrix.one_mul, Matrix.one_mulVec] using h'
  · intro h
    exact congrArg (fun v => elementaryMatrix op *ᵥ v) h

/-- Multiplication on the left applies to the appended column as well. -/
theorem mul_augmented {K : Type u} [Field K] {m n : ℕ}
    (E : Matrix (Fin m) (Fin m) K) (A : Matrix (Fin m) (Fin n) K)
    (b : Fin m → K) :
    E * System.augmentedMatrix A b = System.augmentedMatrix (E * A) (E *ᵥ b) := by
  ext i c
  refine Fin.lastCases ?_ (fun j => ?_) c
  · simp only [Matrix.mul_apply, System.augmentedMatrix_last, Matrix.mulVec_apply_eq_sum]
  · simp only [Matrix.mul_apply, System.augmentedMatrix_castSucc]

theorem applyOp_augmented {K : Type u} [Field K] {m n : ℕ}
    (op : RowOperation K m) (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    applyOp op (System.augmentedMatrix A b) =
      System.augmentedMatrix (applyOp op A) (elementaryMatrix op *ᵥ b) := by
  rw [← elementary_mul, mul_augmented, elementary_mul]

theorem row_operation_solution_iff {K : Type u} [Field K] {m n : ℕ}
    (op : RowOperation K m) (A : Matrix (Fin m) (Fin n) K)
    (b : Fin m → K) (x : Fin n → K) :
    System.IsSolution (applyOp op A) (elementaryMatrix op *ᵥ b) x ↔
      System.IsSolution A b x := by
  rw [← elementary_mul]
  exact elementary_solution_iff op A b x

/-- Every matrix with a last column is its own coefficient/RHS augmentation. -/
theorem reconstruct_augmented {K : Type u} [Field K] {m n : ℕ}
    (M : Matrix (Fin m) (Fin (n + 1)) K) :
    System.augmentedMatrix (fun i j => M i j.castSucc) (fun i => M i (Fin.last n)) = M := by
  ext i c
  refine Fin.lastCases ?_ (fun j => ?_) c
  · exact System.augmentedMatrix_last _ _ i
  · exact System.augmentedMatrix_castSucc _ _ i j

theorem augmented_solution_iff {K : Type u} [Field K] {m n : ℕ}
    (op : RowOperation K m) (M : Matrix (Fin m) (Fin (n + 1)) K) (x : Fin n → K) :
    System.IsSolution (fun i j => applyOp op M i j.castSucc)
      (fun i => applyOp op M i (Fin.last n)) x ↔
    System.IsSolution (fun i j => M i j.castSucc) (fun i => M i (Fin.last n)) x := by
  have h := applyOp_augmented op (fun i j => M i j.castSucc) (fun i => M i (Fin.last n))
  rw [reconstruct_augmented] at h
  have hc := congrArg (fun N : Matrix (Fin m) (Fin (n + 1)) K =>
    fun (i : Fin m) (j : Fin n) => N i j.castSucc) h
  have hb := congrArg (fun N : Matrix (Fin m) (Fin (n + 1)) K =>
    fun i => N i (Fin.last n)) h
  simp only [System.augmentedMatrix_castSucc] at hc
  simp only [System.augmentedMatrix_last] at hb
  rw [hc, hb]
  exact row_operation_solution_iff op _ _ x

/-- Perform a finite list of row operations, from left to right, on all columns. -/
def applySequence {K : Type u} [Field K] {m p : ℕ}
    (ops : List (RowOperation K m)) (M : Matrix (Fin m) (Fin p) K) :
    Matrix (Fin m) (Fin p) K :=
  ops.foldl (fun N op => applyOp op N) M

theorem sequence_solution_iff {K : Type u} [Field K] {m n : ℕ}
    (ops : List (RowOperation K m)) (M : Matrix (Fin m) (Fin (n + 1)) K)
    (x : Fin n → K) :
    System.IsSolution (fun i j => applySequence ops M i j.castSucc)
      (fun i => applySequence ops M i (Fin.last n)) x ↔
    System.IsSolution (fun i j => M i j.castSucc) (fun i => M i (Fin.last n)) x := by
  induction ops generalizing M with
  | nil => exact Iff.rfl
  | cons op ops ih =>
    change System.IsSolution (fun i j => applySequence ops (applyOp op M) i j.castSucc)
      (fun i => applySequence ops (applyOp op M) i (Fin.last n)) x ↔ _
    exact (ih (applyOp op M)).trans (augmented_solution_iff op M x)

theorem sequence_preserves_solutions {K : Type u} [Field K] {m n : ℕ}
    (ops : List (RowOperation K m)) (A : Matrix (Fin m) (Fin n) K)
    (b : Fin m → K) (x : Fin n → K) :
    System.IsSolution
      (fun i j => applySequence ops (System.augmentedMatrix A b) i j.castSucc)
      (fun i => applySequence ops (System.augmentedMatrix A b) i (Fin.last n)) x ↔
      System.IsSolution A b x := by
  simpa only [System.augmentedMatrix_castSucc, System.augmentedMatrix_last] using
    sequence_solution_iff ops (System.augmentedMatrix A b) x

end D05.M01.SolutionInvariance
