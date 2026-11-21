import MathGenome.Internal.Specs.D05.Foundations.VolumeBorelInvertible
import MathGenome.Internal.D05.Foundations.VolumeElementary
import MathGenome.Internal.D05.M01.Elimination
import MathGenome.Internal.D05.M05.DetRowRules
import MathGenome.Internal.D05.M05.DetProduct
import Mathlib.Order.Preorder.Finite
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Finite elementary factorization from Gaussian elimination, followed by
composition of the elementary Borel volume multipliers. No general linear
change-of-volume theorem is used. -/
noncomputable section
open MeasureTheory Set

namespace D05.VolumeBorelInvertible
open D05.VolumeElementary D05.M01.RowOps D05.M01.Elimination

private theorem applyOps_cons {n : ℕ} (op : RowOperation ℝ n) (ops)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    applyOps (op :: ops) A = applyOps ops (applyOp op A) := rfl

/-- Execution of a finite list is multiplication by its accumulated elementary matrix. -/
theorem applyOps_mul {n : ℕ} (ops : List (RowOperation ℝ n))
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    applyOps ops (A * B) = applyOps ops A * B := by
  induction ops generalizing A with
  | nil => rfl
  | cons op ops ih =>
    rw [applyOps_cons, applyOp_mul, ih, applyOps_cons]

theorem applyOps_isUnit {n : ℕ} (ops : List (RowOperation ℝ n))
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A) : IsUnit (applyOps ops A) := by
  induction ops generalizing A with
  | nil => exact hA
  | cons op ops ih =>
    rw [applyOps_cons]
    exact ih _ (by rw [← elementary_mul]; exact (elementary_isUnit op).mul hA)

/-- Reversing the list and inverting each permitted operation undoes the run. -/
theorem applyOps_reverse_inverse {n : ℕ} (ops : List (RowOperation ℝ n))
    (A : Matrix (Fin n) (Fin n) ℝ) :
    applyOps (ops.reverse.map inverse) (applyOps ops A) = A := by
  induction ops generalizing A with
  | nil => rfl
  | cons op ops ih =>
    rw [List.reverse_cons, List.map_append, applyOps_append, applyOps_cons, ih]
    exact inverse_apply op A

/-- In a square invertible reduced form every row has a pivot. Their strict
increase forces the pivot map of `Fin n` to be the identity. -/
theorem reduced_eq_one {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    (hR : R.IsReducedRowEchelon) (hu : IsUnit R) : R = 1 := by
  classical
  have hn : ∀ i, R i ≠ 0 := by
    intro i hz
    exact ((Matrix.isUnit_iff_isUnit_det R).mp hu).ne_zero
      (Matrix.det_eq_zero_of_row_eq_zero i (fun j => congrFun hz j))
  choose p hp using fun i => Matrix.row_ne_zero_iff_exists_isLeadingEntry.mp (hn i)
  have hm : StrictMono p := by
    intro i j hij
    exact ((D05.M01.Echelon.rowEchelon_iff R).mp hR.isRowEchelon).2
      i j (p i) (p j) hij (hp i) (hp j)
  have hd : ∀ i, R.IsLeadingEntry i i := by
    intro i
    simpa only [hm.apply_eq] using hp i
  ext i j
  by_cases h : i = j
  · subst j
    simpa using hR.eq_one (hd i)
  · simpa [Matrix.one_apply, h] using hR.eq_zero_of_ne_of_isLeadingEntry h (hd j)

theorem elementaryFactorization : Spec.elementaryFactorization := by
  intro n A hA
  obtain ⟨ops, hr⟩ := D05.M01.Elimination.exists_reduced A
  have h1 : applyOps ops A = 1 := reduced_eq_one _ hr (applyOps_isUnit ops A hA)
  refine ⟨ops.reverse.map inverse, ?_⟩
  simpa only [h1] using applyOps_reverse_inverse ops A

/-- The coordinate map performed by an elementary row operation on a column. -/
private def operationMap {n : ℕ} (op : RowOperation ℝ n) :
    CoordinateSpace n → CoordinateSpace n :=
  match op with
  | .swap i j _ => coordinatePermutation (Equiv.swap i j)
  | .scale i c _ => coordinateDilation i c
  | .add i j c _ => coordinateShear i j c

private theorem elementary_mulVec {n : ℕ} (op : RowOperation ℝ n) :
    (elementaryMatrix op).mulVec = operationMap op := by
  funext x
  ext k
  have h := congrFun (congrFun
    (elementary_mul op (fun i (_ : Fin 1) => x i)) k) 0
  cases op with
  | swap i j hij => exact h
  | scale i c hc =>
    change (elementaryMatrix (.scale i c hc)).mulVec x k =
      (if k = i then c * x i else x k) at h
    by_cases hk : k = i <;>
      simpa only [operationMap, coordinateDilation, hk, ite_true, ite_false] using h
  | add i j c hij =>
    change (elementaryMatrix (.add i j c hij)).mulVec x k =
      (if k = i then x i + c * x j else x k) at h
    by_cases hk : k = i <;>
      simpa only [operationMap, coordinateShear, hk, ite_true, ite_false] using h

private def operationMultiplier {n : ℕ} (op : RowOperation ℝ n) : ℝ :=
  match op with
  | .swap _ _ _ => -1
  | .scale _ c _ => c
  | .add _ _ _ _ => 1

/-- The three determinant multipliers are obtained from the proved row rules. -/
private theorem elementary_det {n : ℕ} (op : RowOperation ℝ n) :
    (elementaryMatrix op).det = operationMultiplier op := by
  cases op with
  | swap i j hij =>
    have h := D05.M05.DetRowRules.row_swap (1 : Matrix (Fin n) (Fin n) ℝ) i j hij
    change D05.M05.determinant (elementaryMatrix (.swap i j hij)) =
      -D05.M05.determinant 1 at h
    rw [D05.M05.DetDefinition.matrix_det_bridge,
      D05.M05.DetDefinition.matrix_det_bridge, Matrix.det_one] at h
    exact h
  | scale i c hc =>
    have he : (1 : Matrix (Fin n) (Fin n) ℝ).updateRow i (fun j => c * (1 : Matrix (Fin n) (Fin n) ℝ) i j) =
        elementaryMatrix (.scale i c hc) := by
      ext r j
      by_cases hr : r = i <;> simp [Matrix.updateRow, Function.update, elementaryMatrix, applyOp, hr]
    have h := D05.M05.DetRowRules.row_scale (1 : Matrix (Fin n) (Fin n) ℝ) i c
    rw [he, D05.M05.DetDefinition.matrix_det_bridge,
      D05.M05.DetDefinition.matrix_det_bridge, Matrix.det_one, mul_one] at h
    exact h
  | add i j c hij =>
    have he : (1 : Matrix (Fin n) (Fin n) ℝ).updateRow i
        (fun k => (1 : Matrix (Fin n) (Fin n) ℝ) i k + c * (1 : Matrix (Fin n) (Fin n) ℝ) j k) =
        elementaryMatrix (.add i j c hij) := by
      ext r k
      by_cases hr : r = i <;> simp [Matrix.updateRow, Function.update, elementaryMatrix, applyOp, hr]
    have h := D05.M05.DetRowRules.row_add_multiple
      (1 : Matrix (Fin n) (Fin n) ℝ) i j hij c
    rw [he, D05.M05.DetDefinition.matrix_det_bridge,
      D05.M05.DetDefinition.matrix_det_bridge, Matrix.det_one] at h
    exact h

/-- The measure identity is in extended nonnegative reals, so composition does
not need integrability, finiteness, or cancellation of measure values. -/
private def BorelVolume {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ E : Set (CoordinateSpace n), MeasurableSet E →
    MeasurableSet (A.mulVec '' E) ∧
    (volume : Measure (CoordinateSpace n)) (A.mulVec '' E) =
      ENNReal.ofReal |A.det| * (volume : Measure (CoordinateSpace n)) E

private theorem elementaryBorelVolume {n : ℕ} (op : RowOperation ℝ n) :
    BorelVolume (elementaryMatrix op) := by
  intro E hE
  rw [elementary_mulVec, elementary_det]
  cases op with
  | swap i j hij =>
    obtain ⟨hb, hv⟩ := permutationBorelVolume n (Equiv.swap i j) E hE
    refine ⟨hb, ?_⟩
    change volume (coordinatePermutation (Equiv.swap i j) '' E) =
      ENNReal.ofReal |(-1 : ℝ)| * volume E
    rw [abs_neg, abs_one, ENNReal.ofReal_one, one_mul]
    exact hv
  | scale i c hc =>
    exact dilationBorelVolume n i c hc E hE
  | add i j c hij =>
    obtain ⟨hb, hv⟩ := shearBorelVolume n i j c hij E hE
    refine ⟨hb, ?_⟩
    change volume (coordinateShear i j c '' E) =
      ENNReal.ofReal |(1 : ℝ)| * volume E
    rw [abs_one, ENNReal.ofReal_one, one_mul]
    exact hv

private theorem borelVolume_one (n : ℕ) :
    BorelVolume (1 : Matrix (Fin n) (Fin n) ℝ) := by
  intro E hE
  have hid : (1 : Matrix (Fin n) (Fin n) ℝ).mulVec = id := by
    funext x
    exact Matrix.one_mulVec x
  simpa only [hid, Set.image_id, Matrix.det_one, abs_one, ENNReal.ofReal_one, one_mul]
    using And.intro hE (rfl : volume E = volume E)

private theorem borelVolume_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : BorelVolume A) (hB : BorelVolume B) : BorelVolume (A * B) := by
  intro E hE
  obtain ⟨hBE, hvB⟩ := hB E hE
  obtain ⟨hABE, hvA⟩ := hA (B.mulVec '' E) hBE
  have hi : (A * B).mulVec '' E = A.mulVec '' (B.mulVec '' E) := by
    rw [← Set.image_comp]
    congr 1
    funext x
    exact (Matrix.mulVec_mulVec x A B).symm
  rw [hi]
  refine ⟨hABE, ?_⟩
  rw [hvA, hvB]
  have hd : (A * B).det = A.det * B.det := by
    have h := D05.M05.DetProduct.det_mul A B
    rw [D05.M05.DetDefinition.matrix_det_bridge,
      D05.M05.DetDefinition.matrix_det_bridge, D05.M05.DetDefinition.matrix_det_bridge] at h
    exact h
  rw [hd, abs_mul, ENNReal.ofReal_mul (abs_nonneg _), mul_assoc]

private theorem applyOpsBorelVolume {n : ℕ} (ops : List (RowOperation ℝ n))
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : BorelVolume A) : BorelVolume (applyOps ops A) := by
  induction ops generalizing A with
  | nil => exact hA
  | cons op ops ih =>
    rw [applyOps_cons]
    apply ih
    rw [← elementary_mul]
    exact borelVolume_mul _ _ (elementaryBorelVolume op) hA

theorem invertibleBorelVolume : Spec.invertibleBorelVolume := by
  intro n A hA E hE
  obtain ⟨ops, hops⟩ := elementaryFactorization n A hA
  exact hops ▸ applyOpsBorelVolume ops 1 (borelVolume_one n) E hE

end D05.VolumeBorelInvertible
