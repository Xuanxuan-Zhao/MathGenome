import MathGenome.Internal.Specs.D05.M01.RowOps
import MathGenome.Internal.D05.M01.System
import MathGenome.Internal.D05.M04.MatrixProduct

/-! Elementary row operations and their elementary matrices, K05.01.row_ops. -/
namespace D05.M01.RowOps

universe u

open scoped BigOperators

/-- Perform a permitted row operation on all columns of a rectangular matrix. -/
def applyOp {K : Type u} [Field K] {m n : ℕ}
    (op : RowOperation K m) (A : Matrix (Fin m) (Fin n) K) :
    Matrix (Fin m) (Fin n) K :=
  match op with
  | .swap i j _ => fun r c => A (Equiv.swap i j r) c
  | .scale i a _ => fun r c => if r = i then a * A i c else A r c
  | .add i j a _ => fun r c => if r = i then A i c + a * A j c else A r c

/-- Invert a swap, a nonzero rescaling, or a row addition. -/
def inverse {K : Type u} [Field K] {m : ℕ} (op : RowOperation K m) : RowOperation K m :=
  match op with
  | .swap i j h => .swap i j h
  | .scale i a h => .scale i a⁻¹ (inv_ne_zero h)
  | .add i j a h => .add i j (-a) h

/-- The elementary matrix is the result of the operation on the identity. -/
def elementaryMatrix {K : Type u} [Field K] {m : ℕ} (op : RowOperation K m) :
    Matrix (Fin m) (Fin m) K := applyOp op 1

theorem swap_entry {K : Type u} [Field K] {m n : ℕ}
    (i j : Fin m) (h : i ≠ j) (A : Matrix (Fin m) (Fin n) K)
    (r : Fin m) (c : Fin n) :
    applyOp (.swap i j h) A r c =
      if r = i then A j c else if r = j then A i c else A r c := by
  by_cases hr : r = i <;> by_cases hs : r = j <;>
    simp [applyOp, Equiv.swap_apply_def, hr, hs, h.symm]

theorem scale_entry {K : Type u} [Field K] {m n : ℕ}
    (i : Fin m) (a : K) (h : a ≠ 0) (A : Matrix (Fin m) (Fin n) K)
    (r : Fin m) (c : Fin n) :
    applyOp (.scale i a h) A r c = if r = i then a * A i c else A r c := rfl

theorem add_entry {K : Type u} [Field K] {m n : ℕ}
    (i j : Fin m) (a : K) (h : i ≠ j) (A : Matrix (Fin m) (Fin n) K)
    (r : Fin m) (c : Fin n) :
    applyOp (.add i j a h) A r c =
      if r = i then A i c + a * A j c else A r c := rfl

theorem inverse_inverse {K : Type u} [Field K] {m : ℕ} (op : RowOperation K m) :
    inverse (inverse op) = op := by
  cases op <;> simp [inverse]

theorem inverse_apply {K : Type u} [Field K] {m n : ℕ} (op : RowOperation K m)
    (A : Matrix (Fin m) (Fin n) K) : applyOp (inverse op) (applyOp op A) = A := by
  cases op with
  | swap i j h =>
    ext r c
    simp [inverse, applyOp]
  | scale i a ha =>
    ext r c
    by_cases hr : r = i <;> simp [inverse, applyOp, hr, ha]
  | add i j a hij =>
    ext r c
    by_cases hr : r = i <;> simp [inverse, applyOp, hr, hij.symm, neg_mul, add_assoc]

theorem apply_inverse {K : Type u} [Field K] {m n : ℕ} (op : RowOperation K m)
    (A : Matrix (Fin m) (Fin n) K) : applyOp op (applyOp (inverse op) A) = A := by
  simpa only [inverse_inverse] using inverse_apply (inverse op) A

/-- A row operation commutes with multiplying on the right. -/
theorem applyOp_mul {K : Type u} [Field K] {m n p : ℕ} (op : RowOperation K m)
    (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin p) K) :
    applyOp op (A * B) = applyOp op A * B := by
  cases op with
  | swap i j h => rfl
  | scale i a ha =>
    ext r c
    change (if r = i then a * ∑ k, A i k * B k c else ∑ k, A r k * B k c) =
      ∑ k, (if r = i then a * A i k else A r k) * B k c
    by_cases hr : r = i <;> simp [hr, Finset.mul_sum, mul_assoc]
  | add i j a hij =>
    ext r c
    change (if r = i then (∑ k, A i k * B k c) + a * ∑ k, A j k * B k c
        else ∑ k, A r k * B k c) =
      ∑ k, (if r = i then A i k + a * A j k else A r k) * B k c
    by_cases hr : r = i <;>
      simp [hr, Finset.mul_sum, Finset.sum_add_distrib, add_mul, mul_assoc]

theorem elementary_mul {K : Type u} [Field K] {m n : ℕ} (op : RowOperation K m)
    (A : Matrix (Fin m) (Fin n) K) : elementaryMatrix op * A = applyOp op A := by
  simpa only [elementaryMatrix, Matrix.one_mul] using (applyOp_mul op 1 A).symm

theorem elementary_inverse_mul {K : Type u} [Field K] {m : ℕ} (op : RowOperation K m) :
    elementaryMatrix (inverse op) * elementaryMatrix op = 1 := by
  rw [elementary_mul, elementaryMatrix, inverse_apply]

theorem elementary_mul_inverse {K : Type u} [Field K] {m : ℕ} (op : RowOperation K m) :
    elementaryMatrix op * elementaryMatrix (inverse op) = 1 := by
  rw [elementary_mul, elementaryMatrix, apply_inverse]

theorem elementary_isUnit {K : Type u} [Field K] {m : ℕ} (op : RowOperation K m) :
    IsUnit (elementaryMatrix op) := by
  exact ⟨⟨elementaryMatrix op, elementaryMatrix (inverse op),
    elementary_mul_inverse op, elementary_inverse_mul op⟩, rfl⟩

theorem elementary_add_eq {K : Type u} [Field K] {m : ℕ}
    (i j : Fin m) (a : K) (h : i ≠ j) :
    elementaryMatrix (.add i j a h) =
      1 + a • (Matrix.single i j 1 : Matrix (Fin m) (Fin m) K) := by
  ext r c
  by_cases hr : r = i
  · subst r
    by_cases hc : j = c <;>
      simp [elementaryMatrix, applyOp, Matrix.single, Matrix.one_apply, hc]
  · simp [elementaryMatrix, applyOp, Matrix.single, Matrix.one_apply, hr, Ne.symm hr]

theorem matrixUnit_sq_zero {K : Type u} [Field K] {m : ℕ}
    (i j : Fin m) (h : i ≠ j) :
    (Matrix.single i j 1 : Matrix (Fin m) (Fin m) K) * Matrix.single i j 1 = 0 := by
  exact Matrix.single_mul_single_of_ne 1 i j i h.symm 1

theorem shear_mul_shear_inverse {K : Type u} [Field K] {m : ℕ}
    (i j : Fin m) (a : K) (h : i ≠ j) :
    (1 + a • (Matrix.single i j 1 : Matrix (Fin m) (Fin m) K)) *
      (1 - a • Matrix.single i j 1) = 1 := by
  have hinv := elementary_mul_inverse (RowOperation.add i j a h)
  simpa only [inverse, elementary_add_eq, neg_smul, sub_eq_add_neg] using hinv

end D05.M01.RowOps
