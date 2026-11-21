import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.CornerRecurrence
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.DimensionDeterminant
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

noncomputable section
open scoped BigOperators
namespace AdvancedFiniteGroupRepresentations

abbrev factorialReciprocal := Specs.AdvancedFiniteGroupRepresentations.factorialReciprocal
abbrev dimensionMatrix := @Specs.AdvancedFiniteGroupRepresentations.dimensionMatrix
abbrev dimensionDeterminant := @Specs.AdvancedFiniteGroupRepresentations.dimensionDeterminant

@[simp] theorem factorialReciprocal_neg {a : ℤ} (ha : a < 0) :
    factorialReciprocal a = 0 := by
  simp [factorialReciprocal, Specs.AdvancedFiniteGroupRepresentations.factorialReciprocal,
    not_le.mpr ha]

@[simp] theorem factorialReciprocal_nat (a : ℕ) :
    factorialReciprocal (a : ℤ) = 1 / (a.factorial : ℚ) := by
  simp [factorialReciprocal, Specs.AdvancedFiniteGroupRepresentations.factorialReciprocal]

@[simp] theorem factorialReciprocal_zero : factorialReciprocal 0 = 1 := by
  simpa using factorialReciprocal_nat 0

/-- The recurrence is valid also at zero and at negative integers. -/
theorem factorialReciprocal_sub_one (a : ℤ) :
    factorialReciprocal (a - 1) = (a : ℚ) * factorialReciprocal a := by
  by_cases ha : a < 0
  · rw [factorialReciprocal_neg ha, factorialReciprocal_neg (by omega)]
    simp
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ a)
    cases k with
    | zero => norm_num [factorialReciprocal_neg]
    | succ k =>
      have he : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
      rw [he, factorialReciprocal_nat, factorialReciprocal_nat, Nat.factorial_succ]
      push_cast
      have hk : (k + 1 : ℚ) ≠ 0 := by positivity
      field_simp

/-- Every permitted padding of the empty diagram has determinant one. -/
theorem dimensionDeterminant_empty (r : ℕ) :
    dimensionDeterminant emptyPartition r = 1 := by
  have hz (i : ℕ) : rowLength emptyPartition i = 0 :=
    rowLength_zero_of_length_le _ _ (by rw [empty_length]; omega)
  change (dimensionMatrix emptyPartition r).det = 1
  rw [Matrix.det_of_isUpperTriangular]
  · simp [dimensionMatrix, Specs.AdvancedFiniteGroupRepresentations.dimensionMatrix, hz]
  · intro i j hij
    change factorialReciprocal ((rowLength emptyPartition i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ)) = 0
    rw [hz]
    exact factorialReciprocal_neg (by change j.val < i.val at hij; omega)

/-- Determinant expansion with rows in their original order. -/
theorem det_row_expansion {r : ℕ} (A : Matrix (Fin r) (Fin r) ℚ) :
    A.det = ∑ σ : Equiv.Perm (Fin r),
      (Equiv.Perm.sign σ : ℚ) * ∏ i, A i (σ i) := by
  rw [← Matrix.det_transpose A, Matrix.det_apply']
  rfl

/-- Multiplying individual entries of one row in the permutation expansion. -/
theorem det_updateRow_entry_mul {r : ℕ} (A : Matrix (Fin r) (Fin r) ℚ)
    (b : Fin r → ℚ) (i : Fin r) :
    (A.updateRow i (fun j => b j * A i j)).det =
      ∑ σ : Equiv.Perm (Fin r),
        (Equiv.Perm.sign σ : ℚ) * (b (σ i) * ∏ k, A k (σ k)) := by
  rw [det_row_expansion]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ
      (fun k => (A.updateRow i (fun j => b j * A i j)) k (σ k)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun k => A k (σ k)) (Finset.mem_univ i)]
  simp only [Matrix.updateRow_self]
  have he : (∏ k ∈ Finset.univ.erase i,
      (A.updateRow i (fun j => b j * A i j)) k (σ k)) =
      ∏ k ∈ Finset.univ.erase i, A k (σ k) := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [Matrix.updateRow_ne (Finset.mem_erase.mp hk).1]
  rw [he, mul_assoc]

/-- Lower one row before testing whether the resulting shape is a partition. -/
def loweredDimensionMatrix {n : ℕ} (p : Partition n) (r : ℕ) (i : Fin r) :
    Matrix (Fin r) (Fin r) ℚ :=
  (dimensionMatrix p r).updateRow i (fun j =>
    factorialReciprocal ((rowLength p i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ) - 1))

/-- The sum of the formally lowered determinants is the row-size sum times D. -/
theorem sum_loweredDimensionMatrix {n : ℕ} (p : Partition n) (r : ℕ) :
    (∑ i : Fin r, (loweredDimensionMatrix p r i).det) =
      (∑ i : Fin r, (rowLength p i.val : ℚ)) * dimensionDeterminant p r := by
  have he (i : Fin r) : loweredDimensionMatrix p r i =
      (dimensionMatrix p r).updateRow i (fun j =>
        ((rowLength p i.val : ℚ) - (i.val : ℚ) + (j.val : ℚ)) * dimensionMatrix p r i j) := by
    ext k j
    by_cases hk : k = i
    · subst k
      simp only [loweredDimensionMatrix, Matrix.updateRow_self]
      rw [factorialReciprocal_sub_one]
      push_cast
      rfl
    · simp only [loweredDimensionMatrix, Matrix.updateRow_ne hk]
  simp_rw [he, det_updateRow_entry_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  have hs (σ : Equiv.Perm (Fin r)) :
      (∑ i : Fin r, ((rowLength p i.val : ℚ) - (i.val : ℚ) + ((σ i).val : ℚ))) =
        ∑ i : Fin r, (rowLength p i.val : ℚ) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hσ := Equiv.sum_comp σ (fun i : Fin r => (i.val : ℚ))
    rw [hσ]
    ring
  simp_rw [hs]
  change _ = _ * (dimensionMatrix p r).det
  rw [det_row_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

/-- Deletion changes precisely the chosen row by one cell. -/
theorem rowLength_deleteCell {n : ℕ} (p : Partition n) (c : RemovableCell p) (k : ℕ) :
    rowLength (deleteCell p c) k =
      if k = c.val.1 then rowLength p k - 1 else rowLength p k := by
  have hc := (removable_iff_row_end p c.val).mp c.property
  apply eq_of_forall_lt_iff
  intro j
  rw [← cell_iff, deleteCell_cells, Finset.mem_erase, cell_iff]
  by_cases hk : k = c.val.1
  · rw [ite_eq_left hk]
    have he : (k,j) = c.val ↔ j = c.val.2 := by
      constructor
      · exact fun h => congrArg Prod.snd h
      · intro h; exact Prod.ext hk h
    change ((k,j) ≠ c.val ∧ j < rowLength p k) ↔ j < rowLength p k - 1
    simp only [Ne, he]
    rw [hk]
    omega
  · rw [ite_eq_right hk]
    have he : (k,j) ≠ c.val := fun h => hk (congrArg Prod.fst h)
    simp [he]

/-- A deleted diagram needs no more rows than the original diagram. -/
theorem length_deleteCell_le {n : ℕ} (p : Partition n) (c : RemovableCell p) :
    length (deleteCell p c) ≤ length p := by
  rw [length_eq_columnLength_zero, length_eq_columnLength_zero]
  apply le_of_forall_lt
  intro k hk
  rw [← cell_iff_column] at hk ⊢
  rw [deleteCell_cells] at hk
  exact Finset.mem_of_mem_erase hk

/-- The row occupied by a removable cell is among the padded rows. -/
theorem removableCell_row_lt {n : ℕ} (p : Partition n) (c : RemovableCell p)
    (r : ℕ) (hr : length p ≤ r) : c.val.1 < r := by
  have hc := (cell_iff p _ _).mp c.property.1
  change c.val.2 < rowLength p c.val.1 at hc
  by_contra hn
  have hz := rowLength_zero_of_length_le p c.val.1 (by omega)
  omega

/-- A valid formal lowering is exactly the determinant of corner deletion. -/
theorem loweredDimensionMatrix_eq_deleteCell {n : ℕ} (p : Partition n)
    (c : RemovableCell p) (r : ℕ) (hr : length p ≤ r) :
    loweredDimensionMatrix p r ⟨c.val.1, removableCell_row_lt p c r hr⟩ =
      dimensionMatrix (deleteCell p c) r := by
  have hc := (removable_iff_row_end p c.val).mp c.property
  ext i j
  simp only [loweredDimensionMatrix, Matrix.updateRow_apply]
  change (if i = ⟨c.val.1, removableCell_row_lt p c r hr⟩ then
      factorialReciprocal ((rowLength p c.val.1 : ℤ) - (c.val.1 : ℤ) + (j.val : ℤ) - 1)
    else factorialReciprocal ((rowLength p i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ))) =
    factorialReciprocal ((rowLength (deleteCell p c) i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ))
  rw [rowLength_deleteCell]
  by_cases hi : i.val = c.val.1
  · have hi' : i = (⟨c.val.1, removableCell_row_lt p c r hr⟩ : Fin r) := Fin.ext hi
    simp only [hi', ↓reduceIte]
    congr 1
    have hpos : 1 ≤ rowLength p c.val.1 := by omega
    omega
  · have hi' : i ≠ (⟨c.val.1, removableCell_row_lt p c r hr⟩ : Fin r) :=
      fun h => hi (congrArg Fin.val h)
    simp only [hi', hi, ↓reduceIte]

/-- Summing all padded row lengths gives the size of the partition. -/
theorem sum_padded_rowLength {n : ℕ} (p : Partition n) (r : ℕ) (hr : length p ≤ r) :
    (∑ i : Fin r, rowLength p i.val) = n := by
  rw [← Finset.sum_range]
  have hs : (∑ i ∈ Finset.range (length p), rowLength p i) = n := by
    calc
      _ = (parts p).sum := by
        change (∑ i ∈ Finset.range ((diagram p).rowLens.length), (diagram p).rowLen i) =
          (diagram p).rowLens.sum
        rw [YoungDiagram.length_rowLens, YoungDiagram.rowLens, Finset.sum_eq_multiset_sum,
          Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.sum_coe]
      _ = n := parts_sum p
  calc
    _ = ∑ i ∈ Finset.range (length p), rowLength p i := by
      symm
      apply Finset.sum_subset (Finset.range_mono hr)
      intro i hi hni
      apply rowLength_zero_of_length_le
      simpa using hni
    _ = n := hs

/-- A strict drop of row lengths specifies a removable row-end cell. -/
def removableRowCorner {n : ℕ} (p : Partition n) (i : ℕ)
    (hi : rowLength p (i + 1) < rowLength p i) : RemovableCell p :=
  ⟨(i, rowLength p i - 1), (removable_iff_row_end p _).mpr ⟨by dsimp; omega, hi⟩⟩

/-- Invalid deletions vanish: equal adjacent rows, or a zero last row. -/
theorem loweredDimensionMatrix_det_zero {n : ℕ} (p : Partition n) (r : ℕ)
    (hr : length p ≤ r) (i : Fin r)
    (hi : ¬ rowLength p (i.val + 1) < rowLength p i.val) :
    (loweredDimensionMatrix p r i).det = 0 := by
  have heq : rowLength p (i.val + 1) = rowLength p i.val :=
    le_antisymm (rowLength_antitone p (by omega)) (Nat.le_of_not_gt hi)
  by_cases hnext : i.val + 1 < r
  · let k : Fin r := ⟨i.val + 1, hnext⟩
    have hik : i ≠ k := by intro h; have := congrArg Fin.val h; dsimp [k] at this; omega
    apply Matrix.det_zero_of_row_eq hik
    funext j
    rw [loweredDimensionMatrix, Matrix.updateRow_self]
    change factorialReciprocal ((rowLength p i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ) - 1) =
      (loweredDimensionMatrix p r i) k j
    rw [loweredDimensionMatrix, Matrix.updateRow_ne hik.symm]
    change _ = factorialReciprocal ((rowLength p k.val : ℤ) - (k.val : ℤ) + (j.val : ℤ))
    dsimp only [k]
    rw [heq]
    congr 1
    omega
  · have hlast : i.val + 1 = r := by omega
    have hz : rowLength p i.val = 0 := by
      rw [← heq]
      exact rowLength_zero_of_length_le p _ (by omega)
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro j
    rw [loweredDimensionMatrix, Matrix.updateRow_self]
    change factorialReciprocal ((rowLength p i.val : ℤ) - (i.val : ℤ) + (j.val : ℤ) - 1) = 0
    rw [hz]
    exact factorialReciprocal_neg (by have := j.isLt; omega)

/-- The formal sum over padded rows reduces to the sum over actual corners. -/
theorem sum_loweredDimensionMatrix_eq_corners {n : ℕ} (p : Partition n) (r : ℕ)
    (hr : length p ≤ r) :
    letI := Fintype.ofFinite (RemovableCell p)
    (∑ i : Fin r, (loweredDimensionMatrix p r i).det) =
      ∑ c : RemovableCell p, dimensionDeterminant (deleteCell p c) r := by
  classical
  let := Fintype.ofFinite (RemovableCell p)
  let f : RemovableCell p → Fin r := fun c => ⟨c.val.1, removableCell_row_lt p c r hr⟩
  have hf : Function.Injective f := by
    intro c d h
    have hrow : c.val.1 = d.val.1 := congrArg Fin.val h
    have hc := (removable_iff_row_end p c.val).mp c.property
    have hd := (removable_iff_row_end p d.val).mp d.property
    apply Subtype.ext
    apply Prod.ext hrow
    rw [hrow] at hc
    omega
  have hz (i : Fin r) (hi : i ∉ Finset.univ.image f) :
      (loweredDimensionMatrix p r i).det = 0 := by
    apply loweredDimensionMatrix_det_zero p r hr i
    intro hdrop
    apply hi
    let c := removableRowCorner p i.val hdrop
    refine Finset.mem_image.mpr ⟨c, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    rfl
  calc
    _ = ∑ i ∈ Finset.univ.image f, (loweredDimensionMatrix p r i).det := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hz i hi)
    _ = ∑ c : RemovableCell p, (loweredDimensionMatrix p r (f c)).det := by
      rw [Finset.sum_image]
      exact fun a _ b _ h => hf h
    _ = ∑ c : RemovableCell p, dimensionDeterminant (deleteCell p c) r := by
      apply Finset.sum_congr rfl
      intro c _
      change (loweredDimensionMatrix p r ⟨c.val.1, removableCell_row_lt p c r hr⟩).det = _
      rw [loweredDimensionMatrix_eq_deleteCell p c r hr]
      rfl

/-- The determinant itself satisfies the rational form of the corner recurrence. -/
theorem dimensionDeterminant_cornerRecurrence {n : ℕ} (p : Partition n)
    (r : ℕ) (hr : length p ≤ r) :
    letI := Fintype.ofFinite (RemovableCell p)
    (n : ℚ) * dimensionDeterminant p r =
      ∑ c : RemovableCell p, dimensionDeterminant (deleteCell p c) r := by
  have hsum : (∑ i : Fin r, (rowLength p i.val : ℚ)) = (n : ℚ) := by
    exact_mod_cast sum_padded_rowLength p r hr
  rw [← sum_loweredDimensionMatrix_eq_corners p r hr,
    sum_loweredDimensionMatrix, hsum]

/-- Frobenius–Young formula for every permitted padding size, including zero. -/
theorem dimensionDeterminant_formula {n : ℕ} (p : Partition n) (r : ℕ)
    (hr : length p ≤ r) :
    (standardTableauCount p : ℚ) = (n.factorial : ℚ) * dimensionDeterminant p r := by
  induction n using Nat.strong_induction_on generalizing r with
  | h n ih =>
    cases n with
    | zero =>
      have hp : p = emptyPartition := zero_partition_unique p
      subst p
      rw [cornerRecurrence_empty, dimensionDeterminant_empty]
      norm_num
    | succ n =>
      let := Fintype.ofFinite (RemovableCell p)
      have hc := cornerRecurrence p (by omega : 0 < n + 1)
      have hD := dimensionDeterminant_cornerRecurrence p r hr
      calc
        (standardTableauCount p : ℚ) =
            ∑ c : RemovableCell p, (standardTableauCount (deleteCell p c) : ℚ) := by
          exact_mod_cast hc
        _ = ∑ c : RemovableCell p,
            (n.factorial : ℚ) * dimensionDeterminant (deleteCell p c) r := by
          apply Finset.sum_congr rfl
          intro c _
          exact ih n (by omega) (deleteCell p c) r ((length_deleteCell_le p c).trans hr)
        _ = (n.factorial : ℚ) * ((n + 1 : ℕ) : ℚ) * dimensionDeterminant p r := by
          rw [← Finset.mul_sum, ← hD]
          ring
        _ = ((n + 1).factorial : ℚ) * dimensionDeterminant p r := by
          rw [Nat.factorial_succ]
          push_cast
          ring

end AdvancedFiniteGroupRepresentations
