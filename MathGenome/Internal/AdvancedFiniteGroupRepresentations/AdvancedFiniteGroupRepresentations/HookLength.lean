import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.StandardBasisRationalModel
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.DimensionDeterminant
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.HookLength
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Order.Interval.Finset.Fin

noncomputable section
open scoped BigOperators
namespace AdvancedFiniteGroupRepresentations

abbrev hookProduct := @Specs.AdvancedFiniteGroupRepresentations.hookProduct

theorem allHookLengths_positive {n : ℕ} {p : Partition n} (c : Cell p) :
    0 < hookLength c := hookLength_positive c

theorem hookProduct_positive {n : ℕ} (p : Partition n) : 0 < hookProduct p := by
  exact Finset.prod_pos (fun c _ => hookLength_positive c)

@[simp] theorem hookProduct_empty : hookProduct emptyPartition = 1 := by
  have he : IsEmpty (Cell emptyPartition) := by
    refine ⟨fun c => ?_⟩
    have hc := c.property
    change c.val ∈ cells emptyPartition at hc
    rw [empty_cells] at hc
    exact Finset.notMem_empty _ hc
  let := he
  change (∏ c : Cell emptyPartition, hookLength c) = 1
  simp

/-- Transposition swaps the two coordinates of every cell. -/
def transposeCellEquiv {n : ℕ} (p : Partition n) : Cell p ≃ Cell (transpose p) where
  toFun c := ⟨c.val.swap, by
    change c.val.swap ∈ diagram (transpose p)
    rw [transpose_diagram, YoungDiagram.mem_transpose]
    rw [Prod.swap_swap]
    exact c.property⟩
  invFun c := ⟨c.val.swap, by
    have hc : c.val ∈ diagram (transpose p) := c.property
    rw [transpose_diagram, YoungDiagram.mem_transpose] at hc
    exact hc⟩
  left_inv c := Subtype.ext (Prod.swap_swap c.val)
  right_inv c := Subtype.ext (Prod.swap_swap c.val)

@[simp] theorem hookLength_transpose {n : ℕ} {p : Partition n} (c : Cell p) :
    hookLength (transposeCellEquiv p c) = hookLength c := by
  rw [hookLength_formula, hookLength_formula]
  simp only [transposeCellEquiv, Equiv.coe_fn_mk, Prod.fst_swap, Prod.snd_swap,
    transpose_rowLength, transpose_columnLength]
  omega

theorem hookProduct_transpose {n : ℕ} (p : Partition n) :
    hookProduct (transpose p) = hookProduct p := by
  change (∏ c : Cell (transpose p), hookLength c) = ∏ c : Cell p, hookLength c
  rw [← Equiv.prod_comp (transposeCellEquiv p)]
  simp only [hookLength_transpose]

/-- Standard tableaux are preserved by exchanging rows with columns. -/
def standardTableauTransposeEquiv {n : ℕ} (p : Partition n) :
    StandardTableau p ≃ StandardTableau (transpose p) where
  toFun t := ⟨(transposeCellEquiv p).symm.trans t.val, by
    constructor
    · intro a b hab hlt
      exact t.property.2 ((transposeCellEquiv p).symm a)
        ((transposeCellEquiv p).symm b) hab hlt
    · intro a b hab hlt
      exact t.property.1 ((transposeCellEquiv p).symm a)
        ((transposeCellEquiv p).symm b) hab hlt⟩
  invFun t := ⟨(transposeCellEquiv p).trans t.val, by
    constructor
    · intro a b hab hlt
      exact t.property.2 (transposeCellEquiv p a) (transposeCellEquiv p b) hab hlt
    · intro a b hab hlt
      exact t.property.1 (transposeCellEquiv p a) (transposeCellEquiv p b) hab hlt⟩
  left_inv t := by
    apply Subtype.ext
    ext c
    simp
  right_inv t := by
    apply Subtype.ext
    ext c
    simp

theorem standardTableauCount_transpose {n : ℕ} (p : Partition n) :
    standardTableauCount (transpose p) = standardTableauCount p :=
  (Nat.card_congr (standardTableauTransposeEquiv p)).symm

/-- A padded one-row diagram has the single matrix entry `1/n!`. -/
theorem standardTableauCount_singleRow {n : ℕ} (p : Partition n)
    (hp : length p ≤ 1) : standardTableauCount p = 1 := by
  have hn : rowLength p 0 = n := by
    simpa using sum_padded_rowLength p 1 hp
  have hd : dimensionDeterminant p 1 = 1 / (n.factorial : ℚ) := by
    change (dimensionMatrix p 1).det = _
    rw [Matrix.det_fin_one]
    change factorialReciprocal ((rowLength p 0 : ℤ) - 0 + 0) = _
    simp [hn]
  have hf := dimensionDeterminant_formula p 1 hp
  rw [hd] at hf
  have hne : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hf' : (standardTableauCount p : ℚ) = 1 := by
    simpa [hne] using hf
  exact_mod_cast hf'

theorem standardTableauCount_singleColumn {n : ℕ} (p : Partition n)
    (hp : rowLength p 0 ≤ 1) : standardTableauCount p = 1 := by
  rw [← standardTableauCount_transpose p]
  apply standardTableauCount_singleRow
  simpa only [length_eq_columnLength_zero, transpose_columnLength] using hp

theorem specht_finrank_singleRow {n : ℕ} (p : Partition n) (hp : length p ≤ 1) :
    Module.finrank ℂ (SpechtModule p) = 1 := by
  rw [specht_finrank, standardTableauCount_singleRow p hp]

theorem specht_finrank_singleColumn {n : ℕ} (p : Partition n)
    (hp : rowLength p 0 ≤ 1) : Module.finrank ℂ (SpechtModule p) = 1 := by
  rw [specht_finrank, standardTableauCount_singleColumn p hp]

/-- Increasing order for the shifted row lengths: row indices are reversed. -/
def ascendingBeta {n : ℕ} (p : Partition n) (r : ℕ) (i : Fin r) : ℕ :=
  rowLength p i.rev.val + i.val

theorem ascendingBeta_strictMono {n : ℕ} (p : Partition n) (r : ℕ) :
    StrictMono (ascendingBeta p r) := by
  intro i j hij
  have hv : i.val < j.val := hij
  have hr : j.rev.val ≤ i.rev.val := by simp only [Fin.val_rev]; omega
  have hl := rowLength_antitone p hr
  unfold ascendingBeta
  omega

/-- Scaling removes reciprocal factorials, even when the index is negative. -/
theorem factorial_mul_factorialReciprocal (b k : ℕ) :
    (b.factorial : ℚ) * factorialReciprocal ((b : ℤ) - (k : ℤ)) =
      (b.descFactorial k : ℚ) := by
  by_cases hk : k ≤ b
  · have hi : (b : ℤ) - (k : ℤ) = ((b - k : ℕ) : ℤ) := by omega
    rw [hi, factorialReciprocal_nat, mul_one_div]
    have hne : ((b - k).factorial : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (b - k)
    rw [div_eq_iff hne]
    have h := Nat.factorial_mul_descFactorial hk
    rw [mul_comm] at h
    exact_mod_cast h.symm
  · rw [factorialReciprocal_neg (by omega), mul_zero,
      Nat.descFactorial_of_lt (by omega), Nat.cast_zero]

/-- The determinant after reversing both indices and scaling each row. -/
theorem dimensionDeterminant_beta {n : ℕ} (p : Partition n) (r : ℕ) :
    (∏ i : Fin r, ((ascendingBeta p r i).factorial : ℚ)) * dimensionDeterminant p r =
      ∏ i : Fin r, ∏ j ∈ Finset.Ioi i,
        ((ascendingBeta p r j : ℚ) - (ascendingBeta p r i : ℚ)) := by
  let b := ascendingBeta p r
  let A : Matrix (Fin r) (Fin r) ℚ :=
    (dimensionMatrix p r).submatrix Fin.revPerm Fin.revPerm
  have ha (i j : Fin r) :
      A i j = factorialReciprocal ((b i : ℤ) - (j.val : ℤ)) := by
    change factorialReciprocal
      ((rowLength p i.rev.val : ℤ) - (i.rev.val : ℤ) + (j.rev.val : ℤ)) = _
    congr 1
    dsimp [b, ascendingBeta]
    have hi := i.isLt
    have hj := j.isLt
    omega
  have hm : (Matrix.of fun i j : Fin r => ((b i).factorial : ℚ) * A i j) =
      Matrix.of (fun i j : Fin r => (descPochhammer ℚ j.val).eval (b i : ℚ)) := by
    ext i j
    rw [Matrix.of_apply, Matrix.of_apply, ha, factorial_mul_factorialReciprocal,
      descPochhammer_eval_eq_descFactorial]
  have hd := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun i : Fin r => (b i : ℚ)) (fun j : Fin r => descPochhammer ℚ j.val)
    (fun j => descPochhammer_natDegree ℚ j.val)
    (fun j => monic_descPochhammer ℚ j.val)
  rw [← hm, Matrix.det_mul_column, Matrix.det_submatrix_equiv_self] at hd
  rw [Matrix.det_vandermonde] at hd
  exact hd.symm

/-- The coordinate formula, also used on whole finite rows. -/
def rowHookLength {n : ℕ} (p : Partition n) (i j : ℕ) : ℕ :=
  (rowLength p i - (j + 1)) + (columnLength p j - (i + 1)) + 1

theorem rowHookLength_eq {n : ℕ} {p : Partition n} (c : Cell p) :
    rowHookLength p c.val.1 c.val.2 = hookLength c :=
  (hookLength_formula c).symm

/-- Along a row the hook lengths strictly decrease. -/
theorem rowHookLength_strictAnti {n : ℕ} (p : Partition n) (i : ℕ) :
    StrictAnti (fun j : Fin (rowLength p i) => rowHookLength p i j.val) := by
  intro j k hjk
  have hj := j.isLt
  have hk := k.isLt
  have hv : j.val < k.val := hjk
  have hc : columnLength p k.val ≤ columnLength p j.val :=
    (diagram p).colLen_anti _ _ (Nat.le_of_lt hv)
  dsimp [rowHookLength]
  omega

/-- In a padded row, hooks and beta differences partition `1,...,beta`. -/
theorem rowHookLength_partition {n : ℕ} (p : Partition n) (r : ℕ)
    (hr : length p ≤ r) (i : Fin r) :
    let H := (Finset.univ : Finset (Fin (rowLength p i.rev.val))).image
      (fun j => rowHookLength p i.rev.val j.val)
    let E := (Finset.Iio i).image (fun k => ascendingBeta p r i - ascendingBeta p r k)
    Disjoint H E ∧ H ∪ E = Finset.Icc 1 (ascendingBeta p r i) := by
  classical
  let b := ascendingBeta p r
  let H := (Finset.univ : Finset (Fin (rowLength p i.rev.val))).image
    (fun j => rowHookLength p i.rev.val j.val)
  let E := (Finset.Iio i).image (fun k => b i - b k)
  have hb := ascendingBeta_strictMono p r
  have hH : ∀ h ∈ H, h ∈ Finset.Icc 1 (b i) := by
    intro h hh
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hh
    have hj := j.isLt
    have hcol : columnLength p j.val ≤ r := by
      have h := (diagram p).colLen_anti 0 j.val (Nat.zero_le _)
      change columnLength p j.val ≤ columnLength p 0 at h
      rw [← length_eq_columnLength_zero] at h
      omega
    have hc : i.rev.val < columnLength p j.val := by
      exact (cell_iff_column p _ _).mp ((cell_iff p _ _).mpr hj)
    simp only [Finset.mem_Icc]
    dsimp [rowHookLength, b, ascendingBeta]
    have hi := i.isLt
    simp only [Fin.val_rev] at hj hc ⊢
    omega
  have hE : ∀ e ∈ E, e ∈ Finset.Icc 1 (b i) := by
    intro e he
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp he
    have hlt := hb (Finset.mem_Iio.mp hk)
    change b k < b i at hlt
    simp only [Finset.mem_Icc]
    omega
  have hdis : Disjoint H E := by
    apply Finset.disjoint_left.mpr
    intro h hh he
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp he
    have hki' : k < i := Finset.mem_Iio.mp hk
    have hki : k.val < i.val := hki'
    have hbeta := hb (Finset.mem_Iio.mp hk)
    have hj := j.isLt
    have hci : i.rev.val < columnLength p j.val :=
      (cell_iff_column p _ _).mp ((cell_iff p _ _).mpr hj)
    have hi := i.isLt
    have hk' := k.isLt
    by_cases hjk : j.val < rowLength p k.rev.val
    · have hck : k.rev.val < columnLength p j.val :=
        (cell_iff_column p _ _).mp ((cell_iff p _ _).mpr hjk)
      dsimp [rowHookLength, b, ascendingBeta] at he hbeta
      simp only [Fin.val_rev] at hj hjk hci hck he hbeta
      omega
    · have hck : columnLength p j.val ≤ k.rev.val := by
        by_contra hn
        have hm := (cell_iff_column p _ _).mpr (Nat.lt_of_not_ge hn)
        exact hjk ((cell_iff p _ _).mp hm)
      dsimp [rowHookLength, b, ascendingBeta] at he hbeta
      simp only [Fin.val_rev] at hj hjk hci hck he hbeta
      omega
  have hcardH : H.card = rowLength p i.rev.val := by
    rw [Finset.card_image_of_injective _ (rowHookLength_strictAnti p i.rev.val).injective]
    simp
  have hcardE : E.card = i.val := by
    rw [Finset.card_image_iff.mpr]
    · exact Fin.card_Iio i
    · intro k hk l hl he
      have hk' := hb (Finset.mem_Iio.mp hk)
      have hl' := hb (Finset.mem_Iio.mp hl)
      apply hb.injective
      change b k < b i at hk'
      change b l < b i at hl'
      change b i - b k = b i - b l at he
      change b k = b l
      omega
  refine ⟨hdis, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hH x hx
    · exact hE x hx
  · rw [Finset.card_union_of_disjoint hdis, hcardH, hcardE, Nat.card_Icc]
    dsimp [b, ascendingBeta]
    omega

private theorem prod_Icc_id_factorial (b : ℕ) :
    (∏ k ∈ Finset.Icc 1 b, k) = b.factorial := by
  rw [Nat.factorial_eq_prod_range_add_one]
  apply Finset.prod_bij (fun k _ => k - 1)
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    omega
  · intro k hk l hl he
    simp only [Finset.mem_Icc] at hk hl
    omega
  · intro k hk
    refine ⟨k + 1, ?_, by omega⟩
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Icc]
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    omega

/-- Product of the hooks in one row times its excluded factors. -/
theorem rowHookLength_product {n : ℕ} (p : Partition n) (r : ℕ)
    (hr : length p ≤ r) (i : Fin r) :
    (∏ j : Fin (rowLength p i.rev.val), rowHookLength p i.rev.val j.val) *
      (∏ k ∈ Finset.Iio i, (ascendingBeta p r i - ascendingBeta p r k)) =
        (ascendingBeta p r i).factorial := by
  classical
  have hp := rowHookLength_partition p r hr i
  dsimp only at hp
  have hprod := congrArg (fun s : Finset ℕ => ∏ k ∈ s, k) hp.2
  rw [Finset.prod_union hp.1] at hprod
  rw [Finset.prod_image (fun a _ b _ h =>
    (rowHookLength_strictAnti p i.rev.val).injective h)] at hprod
  have hinj : Set.InjOn (fun k => ascendingBeta p r i - ascendingBeta p r k)
      (↑(Finset.Iio i) : Set (Fin r)) := by
    intro k hk l hl he
    have hk' := ascendingBeta_strictMono p r (Finset.mem_Iio.mp hk)
    have hl' := ascendingBeta_strictMono p r (Finset.mem_Iio.mp hl)
    apply (ascendingBeta_strictMono p r).injective
    change ascendingBeta p r i - ascendingBeta p r k =
      ascendingBeta p r i - ascendingBeta p r l at he
    omega
  rw [Finset.prod_image hinj] at hprod
  exact hprod.trans (prod_Icc_id_factorial _)

/-- Index all cells by a padded row and an index within that row. -/
def paddedRowCellEquiv {n : ℕ} (p : Partition n) (r : ℕ) (hr : length p ≤ r) :
    (Σ i : Fin r, Fin (rowLength p i.val)) ≃ Cell p where
  toFun c := ⟨(c.1.val, c.2.val), (cell_iff p _ _).mpr c.2.isLt⟩
  invFun c := ⟨⟨c.val.1, by
      have hc := (cell_iff p _ _).mp c.property
      change c.val.2 < rowLength p c.val.1 at hc
      by_contra hn
      have hz := rowLength_zero_of_length_le p c.val.1 (by omega)
      rw [hz] at hc
      omega⟩, ⟨c.val.2, (cell_iff p _ _).mp c.property⟩⟩
  left_inv c := by rcases c with ⟨i, j⟩; rfl
  right_inv c := by apply Subtype.ext; rfl

theorem hookProduct_eq_rowProducts {n : ℕ} (p : Partition n) (r : ℕ)
    (hr : length p ≤ r) :
    hookProduct p = ∏ i : Fin r,
      ∏ j : Fin (rowLength p i.rev.val), rowHookLength p i.rev.val j.val := by
  have h := Equiv.prod_comp (paddedRowCellEquiv p r hr) (fun c : Cell p => hookLength c)
  rw [Fintype.prod_sigma] at h
  change (∏ i : Fin r, ∏ j : Fin (rowLength p i.val),
    hookLength (paddedRowCellEquiv p r hr ⟨i,j⟩)) = hookProduct p at h
  have he (i : Fin r) (j : Fin (rowLength p i.val)) :
      hookLength (paddedRowCellEquiv p r hr ⟨i,j⟩) = rowHookLength p i.val j.val :=
    (rowHookLength_eq _).symm
  simp_rw [he] at h
  rw [← h]
  exact (Equiv.prod_comp Fin.revPerm
    (fun i : Fin r => ∏ j : Fin (rowLength p i.val), rowHookLength p i.val j.val)).symm

/-- Multiplying over the lower triangular and upper triangular pairs is the same. -/
private theorem prod_beta_differences {r : ℕ} (b : Fin r → ℕ) :
    (∏ i : Fin r, ∏ k ∈ Finset.Iio i, (b i - b k)) =
      ∏ k : Fin r, ∏ i ∈ (Finset.Ioi k : Finset (Fin r)), (b i - b k) := by
  simp_rw [← Finset.filter_gt_eq_Iio, ← Finset.filter_lt_eq_Ioi, Finset.prod_filter]
  rw [Finset.prod_comm]

/-- The full hook factorization, stated without division in the naturals. -/
theorem hookProduct_beta {n : ℕ} (p : Partition n) (r : ℕ) (hr : length p ≤ r) :
    hookProduct p *
      (∏ i : Fin r, ∏ j ∈ (Finset.Ioi i : Finset (Fin r)), (ascendingBeta p r j - ascendingBeta p r i)) =
        ∏ i : Fin r, (ascendingBeta p r i).factorial := by
  rw [hookProduct_eq_rowProducts p r hr, ← prod_beta_differences, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact rowHookLength_product p r hr i

/-- Evaluation of the dimension determinant by the actual hooks. -/
theorem dimensionDeterminant_eq_inv_hookProduct {n : ℕ} (p : Partition n)
    (r : ℕ) (hr : length p ≤ r) :
    dimensionDeterminant p r = 1 / (hookProduct p : ℚ) := by
  let F : ℚ := ∏ i : Fin r, ((ascendingBeta p r i).factorial : ℚ)
  let G : ℕ := ∏ i : Fin r, ∏ j ∈ Finset.Ioi i,
    (ascendingBeta p r j - ascendingBeta p r i)
  have hG : (G : ℚ) = ∏ i : Fin r, ∏ j ∈ Finset.Ioi i,
      ((ascendingBeta p r j : ℚ) - (ascendingBeta p r i : ℚ)) := by
    dsimp [G]
    simp only [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro j hj
    rw [Nat.cast_sub (Nat.le_of_lt (ascendingBeta_strictMono p r (Finset.mem_Ioi.mp hj)))]
  have hD : F * dimensionDeterminant p r = (G : ℚ) := by
    rw [hG]
    exact dimensionDeterminant_beta p r
  have hprod : (hookProduct p : ℚ) * (G : ℚ) = F := by
    have h := congrArg (fun a : ℕ => (a : ℚ)) (hookProduct_beta p r hr)
    simpa only [Nat.cast_mul, Nat.cast_prod, F, G] using h
  have hF : F ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact_mod_cast Nat.factorial_ne_zero (ascendingBeta p r i)
  have hHD : (hookProduct p : ℚ) * dimensionDeterminant p r = 1 := by
    apply mul_left_cancel₀ hF
    calc
      F * ((hookProduct p : ℚ) * dimensionDeterminant p r) =
          (hookProduct p : ℚ) * (F * dimensionDeterminant p r) := by ring
      _ = (hookProduct p : ℚ) * (G : ℚ) := by rw [hD]
      _ = F := hprod
      _ = F * 1 := (mul_one F).symm
  have hH : (hookProduct p : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hookProduct_positive p))
  apply (eq_div_iff hH).mpr
  simpa only [mul_comm] using hHD

/-- Hook-length formula for standard tableaux, with factorial and product cast to ℚ. -/
theorem hookLength_formula_count {n : ℕ} (p : Partition n) :
    (standardTableauCount p : ℚ) = (n.factorial : ℚ) / (hookProduct p : ℚ) := by
  rw [dimensionDeterminant_formula p (length p) le_rfl,
    dimensionDeterminant_eq_inv_hookProduct p (length p) le_rfl, mul_one_div]

/-- Both equalities in FR-B08, including the complex Specht dimension. -/
theorem hookLength_formula_dimension {n : ℕ} (p : Partition n) :
    Module.finrank ℂ (SpechtModule p) = standardTableauCount p ∧
    (Module.finrank ℂ (SpechtModule p) : ℚ) =
      (n.factorial : ℚ) / (hookProduct p : ℚ) := by
  exact ⟨specht_finrank p, by rw [specht_finrank]; exact hookLength_formula_count p⟩

end AdvancedFiniteGroupRepresentations
