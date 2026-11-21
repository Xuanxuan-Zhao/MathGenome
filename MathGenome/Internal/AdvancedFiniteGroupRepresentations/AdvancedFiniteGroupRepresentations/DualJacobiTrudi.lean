import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.SchurTableauFormula
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.DualJacobiTrudi
import Mathlib.Data.Finset.Sort

noncomputable section
open scoped BigOperators Matrix
open Classical
set_option maxHeartbeats 800000
namespace AdvancedFiniteGroupRepresentations

abbrev dualJacobiTrudiMatrix := @Specs.AdvancedFiniteGroupRepresentations.dualJacobiTrudiMatrix
abbrev dualJacobiTrudi := @Specs.AdvancedFiniteGroupRepresentations.dualJacobiTrudi

/-- The number of rows of the transposed shape is the width of the shape. -/
theorem length_transpose_eq_width {n : ℕ} (p : Partition n) :
    length (transpose p) = rowLength p 0 := by
  rw [length_eq_columnLength_zero, transpose_columnLength]

theorem dualJacobiTrudi_succ {n : ℕ} (p : Partition n) (r q : ℕ)
    (hp : rowLength p 0 ≤ q) :
    dualJacobiTrudi p r (q+1) = dualJacobiTrudi p r q := by
  let A := dualJacobiTrudiMatrix p r (q+1)
  have hrow : rowLength (transpose p) q = 0 :=
    rowLength_zero_of_length_le _ q (by rw [length_transpose_eq_width]; exact hp)
  have hlast : A (Fin.last q) (Fin.last q) = 1 := by
    change e r ((rowLength (transpose p) q : ℤ) - (q : ℤ) + (q : ℤ)) = 1
    simpa only [hrow, Nat.cast_zero, zero_sub, neg_add_cancel] using e_zero r
  have hzero (j : Fin q) : A (Fin.last q) j.castSucc = 0 := by
    change e r ((rowLength (transpose p) q : ℤ) - (q : ℤ) + (j.val : ℤ)) = 0
    rw [hrow]
    apply e_neg
    have := j.isLt
    omega
  change A.det = _
  rw [Matrix.det_succ_row A (Fin.last q), Fin.sum_univ_castSucc]
  simp only [Fin.val_last, Fin.succAbove_last, hlast, hzero, mul_zero, zero_mul,
    Finset.sum_const_zero, zero_add, mul_one]
  rw [← two_mul, pow_mul]
  simp
  rfl

theorem dualJacobiTrudi_stable {n : ℕ} (p : Partition n) (r q k : ℕ)
    (hp : rowLength p 0 ≤ q) (hqk : q ≤ k) :
    dualJacobiTrudi p r k = dualJacobiTrudi p r q := by
  induction k, hqk using Nat.le_induction with
  | base => rfl
  | @succ k hqk ih => rw [dualJacobiTrudi_succ p r k (hp.trans hqk), ih]

theorem empty_dualJacobiTrudi (r q : ℕ) :
    dualJacobiTrudi emptyPartition r q = 1 := by
  have hw : rowLength emptyPartition 0 = 0 :=
    rowLength_zero_of_length_le _ _ (by rw [empty_length])
  rw [dualJacobiTrudi_stable emptyPartition r 0 q (by omega) (Nat.zero_le _)]
  exact Matrix.det_isEmpty

theorem e_no_variables (k : ℤ) (hk : 0 < k) : e 0 k = 0 :=
  e_eq_zero_of_lt_degree 0 k (by omega)

theorem dualJacobiTrudi_no_variables {n : ℕ} (p : Partition n) (q : ℕ)
    (hp : rowLength p 0 ≤ q) :
    dualJacobiTrudi p 0 q = if n = 0 then 1 else 0 := by
  split_ifs with hn
  · subst n
    rw [zero_partition_unique p, empty_dualJacobiTrudi]
  · have hfirst := rowLength_zero_pos_of_size_pos (transpose p) (Nat.pos_of_ne_zero hn)
    have hq : 0 < q := by
      have hw := rowLength_zero_pos_of_size_pos p (Nat.pos_of_ne_zero hn)
      omega
    apply Matrix.det_eq_zero_of_row_eq_zero ⟨0, hq⟩
    intro j
    change e 0 ((rowLength (transpose p) 0 : ℤ) - (0 : ℤ) + (j.val : ℤ)) = 0
    apply e_no_variables
    omega

/-- Forget the order of a strictly increasing word. -/
def strictWordSubset {r k : ℕ} (w : {w : Word r k // StrictMono w}) :
    {s : Finset (Fin r) // s.card = k} :=
  ⟨Finset.univ.image w.val, by rw [Finset.card_image_of_injective _ w.property.injective]; simp⟩

theorem strictWordSubset_bijective (r k : ℕ) :
    Function.Bijective (@strictWordSubset r k) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    apply (a.property.range_inj_of_wellFoundedLT b.property).mp
    have hs := congrArg Subtype.val hab
    change Finset.univ.image a.val = Finset.univ.image b.val at hs
    ext x
    have hh := Finset.ext_iff.mp hs x
    simpa only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using hh
  · intro s
    refine ⟨⟨s.val.orderEmbOfFin s.property, (s.val.orderEmbOfFin s.property).strictMono⟩, ?_⟩
    apply Subtype.ext
    exact Finset.image_orderEmbOfFin_univ _ _

/-- The upstream elementary polynomial is the library's literal subset sum. -/
theorem e_eq_esymm (r k : ℕ) : e r (k : ℤ) = MvPolynomial.esymm (Fin r) ℂ k := by
  rw [e_nat]
  change (∑ w ∈ Finset.univ.filter StrictMono, wordWeight w) = _
  rw [Finset.sum_subtype (p := fun w : Word r k => StrictMono w) _ (fun w => by simp)]
  rw [MvPolynomial.esymm_eq_sum_subtype]
  apply Fintype.sum_bijective strictWordSubset (strictWordSubset_bijective r k) _ _
  intro w
  change (∏ i : Fin k, MvPolynomial.X (w.val i)) = ∏ j ∈ Finset.univ.image w.val, MvPolynomial.X j
  rw [Finset.prod_image w.property.injective.injOn]

lemma multiset_esymm_cons {R : Type*} [CommSemiring R] (a : R) (s : Multiset R) (k : ℕ) :
    (a ::ₘ s).esymm (k+1) = s.esymm (k+1) + a * s.esymm k := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add,
    Multiset.sum_add, Multiset.map_map, Function.comp_def, Multiset.prod_cons]
  rw [Multiset.sum_map_mul_left]

/-- Adjoining the last letter adds it either once or not at all. -/
theorem e_succ_alphabet_nat (r k : ℕ) :
    e (r+1) ((k+1 : ℕ) : ℤ) =
      MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r+1)) (e r ((k+1 : ℕ) : ℤ)) +
      MvPolynomial.X (Fin.last r) *
        MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r+1)) (e r (k : ℤ)) := by
  simp_rw [e_eq_esymm]
  have hf (j : ℕ) : MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r+1))
      (MvPolynomial.esymm (Fin r) ℂ j) =
      ((Finset.univ : Finset (Fin r)).val.map (fun i =>
        (MvPolynomial.X i.castSucc : Alphabet (r+1)))).esymm j := by
    simpa only [MvPolynomial.rename_eq_aeval, Function.comp_def] using
      (MvPolynomial.aeval_esymm_eq_multiset_esymm (σ := Fin r) (R := ℂ) j
        (fun i => (MvPolynomial.X i.castSucc : Alphabet (r+1))))
  rw [hf, hf, MvPolynomial.esymm_eq_multiset_esymm]
  have hm : ((Finset.univ : Finset (Fin (r+1))).val.map
      (MvPolynomial.X : Fin (r+1) → Alphabet (r+1))) =
      MvPolynomial.X (Fin.last r) ::ₘ
        ((Finset.univ : Finset (Fin r)).val.map (fun i => MvPolynomial.X i.castSucc)) := by
    rw [Fin.univ_castSuccEmb, Finset.cons_val, Finset.map_val, Multiset.map_cons, Multiset.map_map]
    rfl
  rw [hm, multiset_esymm_cons]


/-- The elementary branching identity, including negative degrees. -/
theorem e_succ_alphabet (r : ℕ) (k : ℤ) :
    e (r+1) k = MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r+1)) (e r k) +
      MvPolynomial.X (Fin.last r) *
        MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r+1)) (e r (k-1)) := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [e_neg _ _ hk, e_neg _ _ hk, e_neg _ _ (by omega), map_zero, mul_zero, add_zero]
  · subst k
    rw [e_zero, e_zero, e_neg _ _ (by omega), map_one, map_zero, mul_zero, add_zero]
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, k = (j+1 : ℕ) := ⟨k.toNat - 1, by omega⟩
    subst k
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using e_succ_alphabet_nat r j

/-- Express the two choices by their resulting nonnegative exponent. -/
theorem e_succ_alphabet_shift (r b d : ℕ) :
    e (r+1) ((b : ℤ) - d) = ∑ t ∈ Finset.Icc (b-1) b,
      MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r+1)) (e r ((t : ℤ) - d)) *
        (MvPolynomial.X (Fin.last r) : Alphabet (r+1)) ^ (b-t) := by
  cases b with
  | zero =>
    simp only [Nat.zero_sub, Finset.Icc_self, Finset.sum_singleton, pow_zero, mul_one]
    rw [e_succ_alphabet]
    simp only [Nat.cast_zero]
    rw [e_neg r ((0 : ℤ) - d - 1) (by omega), map_zero, mul_zero, add_zero]
  | succ b =>
    have hs : Finset.Icc (b+1-1) (b+1) = {b, b+1} := by ext t; simp; omega
    rw [hs, Finset.sum_pair (by omega)]
    simp only [Nat.add_sub_cancel_left, pow_one, tsub_self, pow_zero, mul_one]
    rw [e_succ_alphabet]
    have hi : ((b+1 : ℕ) : ℤ) - d - 1 = (b : ℤ) - d := by omega
    rw [hi]
    ring

def shiftedEDet (r : ℕ) {m : ℕ} (b : Fin m → ℕ) : Alphabet r :=
  (Matrix.of fun i j : Fin m => e r ((b i : ℤ) - (staircase m j : ℤ))).det

theorem shiftedEDet_shiftedPartition {n : ℕ} (p : Partition n) (r m : ℕ) :
    shiftedEDet r (shiftedPartition m (transpose p)) = dualJacobiTrudi p r m := by
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  change e r _ = e r _
  congr 1
  have hi := i.isLt
  have hj := j.isLt
  change ((rowLength (transpose p) i.val + (m-1-i.val) : ℕ) : ℤ) -
    ((m-1-j.val : ℕ) : ℤ) = (rowLength (transpose p) i.val : ℤ) - i.val + j.val
  omega

def EVectorBounded {m : ℕ} (b t : Fin m → ℕ) : Prop :=
  ∀ i, t i ≤ b i ∧ b i ≤ t i + 1

theorem shiftedEDet_succ_expansion (r : ℕ) {m : ℕ} (b : Fin m → ℕ) :
    shiftedEDet (r+1) b =
      ∑ t ∈ Fintype.piFinset (fun i => Finset.Icc (b i - 1) (b i)),
        MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r+1)) (shiftedEDet r t) *
          (MvPolynomial.X (Fin.last r) : Alphabet (r+1)) ^ ((∑ i, b i) - ∑ i, t i) := by
  let z : Alphabet (r+1) := MvPolynomial.X (Fin.last r)
  let ι : Alphabet r →ₐ[ℂ] Alphabet (r+1) := MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r+1))
  let g : Fin m → ℕ → (Fin m → Alphabet (r+1)) :=
    fun i t j => z ^ (b i-t) * ι (e r ((t : ℤ) - (staircase m j : ℤ)))
  have he : (Matrix.of fun i j : Fin m => e (r+1) ((b i : ℤ) - (staircase m j : ℤ))) =
      fun i => ∑ t ∈ Finset.Icc (b i-1) (b i), g i t := by
    funext i j
    simp only [Matrix.of_apply, Finset.sum_apply, g]
    rw [e_succ_alphabet_shift]
    apply Finset.sum_congr rfl
    intro t _
    exact mul_comm _ _
  change Matrix.det _ = _
  rw [he]
  have hm := Matrix.detRowAlternating.toMultilinearMap.map_sum_finset g
    (fun i => Finset.Icc (b i-1) (b i))
  change Matrix.det _ = _ at hm
  rw [hm]
  apply Finset.sum_congr rfl
  intro t ht
  have ht : ∀ i, t i ≤ b i := fun i => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp ht i)).2
  change (Matrix.of fun i j => z ^ (b i-t i) * ι (e r ((t i : ℤ) - (staircase m j : ℤ)))).det = _
  erw [Matrix.det_mul_column (fun i => z ^ (b i-t i))
    (Matrix.of fun i j => ι (e r ((t i : ℤ) - (staircase m j : ℤ)))),
    Finset.prod_pow_eq_pow_sum, Finset.sum_tsub_distrib _ (fun i _ => ht i)]
  rw [mul_comm]
  congr 1
  change _ = ι.toRingHom (Matrix.of fun i j : Fin m => e r ((t i : ℤ) - (staircase m j : ℤ))).det
  rw [RingHom.map_det]
  rfl

/-- A bounded one-step decrement of a strict list is weakly decreasing. -/
theorem EVectorBounded.antitone {m : ℕ} {b t : Fin m → ℕ}
    (ht : EVectorBounded b t) (hb : StrictAnti b) : Antitone t := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hij | rfl
  · have hh := hb hij
    have hi := ht i
    have hj := ht j
    omega
  · rfl

/-- Non-strict lists in the expansion have two equal determinant rows. -/
theorem shiftedEDet_eq_zero_of_not_strictAnti (r : ℕ) {m : ℕ} (b t : Fin m → ℕ)
    (hb : StrictAnti b) (ht : EVectorBounded b t) (hanti : ¬ StrictAnti t) :
    shiftedEDet r t = 0 := by
  by_contra hdet
  have hinj : Function.Injective t := by
    intro i j hij
    by_contra hne
    apply hdet
    apply Matrix.det_zero_of_row_eq hne
    funext k
    change e r _ = e r _
    rw [hij]
  exact hanti ((ht.antitone hb).strictAnti_of_injective hinj)

theorem shiftedEDet_succ_strict (r : ℕ) {m : ℕ} (b : Fin m → ℕ) (hb : StrictAnti b) :
    shiftedEDet (r+1) b =
      ∑ t ∈ (Fintype.piFinset (fun i => Finset.Icc (b i-1) (b i))).filter StrictAnti,
        MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r+1)) (shiftedEDet r t) *
          (MvPolynomial.X (Fin.last r) : Alphabet (r+1)) ^ ((∑ i, b i) - ∑ i, t i) := by
  rw [shiftedEDet_succ_expansion]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro t ht hn
  have hanti : ¬ StrictAnti t := by simpa only [Finset.mem_filter, ht, true_and] using hn
  have hbound : EVectorBounded b t := by
    intro i
    have hi := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp ht i)
    constructor <;> omega
  rw [shiftedEDet_eq_zero_of_not_strictAnti r b t hb hbound hanti, map_zero, zero_mul]

theorem diagram_rowLen_mono {D P : YoungDiagram} (hDP : D ≤ P) (i : ℕ) :
    D.rowLen i ≤ P.rowLen i := by
  by_contra h
  have hc : (i, P.rowLen i) ∈ D := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
  have hh := YoungDiagram.mem_iff_lt_rowLen.mp (hDP hc)
  omega

theorem diagram_colLen_mono {D P : YoungDiagram} (hDP : D ≤ P) (j : ℕ) :
    D.colLen j ≤ P.colLen j := by
  simpa only [YoungDiagram.rowLen_transpose] using
    diagram_rowLen_mono (YoungDiagram.transpose_mono hDP) j

/-- Horizontal strips have at most one removed cell in every column. -/
theorem horizontalStrip_iff_column_bounds (D P : YoungDiagram) :
    (∀ i, P.rowLen (i+1) ≤ D.rowLen i) ↔ ∀ j, P.colLen j ≤ D.colLen j+1 := by
  constructor
  · intro hh j
    by_contra h
    have hc : (D.colLen j+1, j) ∈ P := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have hs := hh (D.colLen j)
    have hr := YoungDiagram.mem_iff_lt_rowLen.mp hc
    have hd : (D.colLen j, j) ∈ D := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hd := YoungDiagram.mem_iff_lt_colLen.mp hd
    omega
  · intro hh i
    by_contra h
    have hc : (i+1, D.rowLen i) ∈ P := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hs := hh (D.rowLen i)
    have hr := YoungDiagram.mem_iff_lt_colLen.mp hc
    have hd : (i, D.rowLen i) ∈ D := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have hd := YoungDiagram.mem_iff_lt_rowLen.mp hd
    omega

theorem subshape_width_le {n : ℕ} {p : Partition n} (d : HorizontalSubshape p) :
    rowLength (subshapePartition d) 0 ≤ rowLength p 0 := by
  change (diagram (subshapePartition d)).rowLen 0 ≤ (diagram p).rowLen 0
  rw [diagram_subshapePartition]
  exact diagram_rowLen_mono d.property.1 0

/-- Transposing a horizontal deletion lowers every row length by at most one. -/
theorem subshape_transpose_shifted_mem {n m : ℕ} (p : Partition n)
    (d : HorizontalSubshape p) :
    EVectorBounded (shiftedPartition m (transpose p))
      (shiftedPartition m (transpose (subshapePartition d))) := by
  intro i
  have hle := diagram_colLen_mono d.property.1 i.val
  have hdiff := (horizontalStrip_iff_column_bounds d.val (diagram p)).mp d.property.2 i.val
  have hd : columnLength (subshapePartition d) i.val = d.val.colLen i.val := by
    change (diagram (subshapePartition d)).colLen _ = _
    rw [diagram_subshapePartition]
  simp only [shiftedPartition, Specs.AdvancedFiniteGroupRepresentations.shiftedPartition,
    transpose_rowLength, hd]
  change d.val.colLen i.val + _ ≤ (diagram p).colLen i.val + _ ∧
    (diagram p).colLen i.val + _ ≤ d.val.colLen i.val + _ + 1
  omega

/-- Each strict one-step decrement list gives a unique horizontal subdiagram
of the untransposed shape. -/
theorem exists_subshape_of_elementary_vector {n m : ℕ} (p : Partition n)
    (hp : rowLength p 0 ≤ m) (t : Fin m → ℕ)
    (ht : EVectorBounded (shiftedPartition m (transpose p)) t) (hanti : StrictAnti t) :
    ∃ d : HorizontalSubshape p,
      shiftedPartition m (transpose (subshapePartition d)) = t := by
  have hdeg : staircaseDegree m ≤ ∑ i, t i :=
    Finset.sum_le_sum (fun i _ => (strictAnti_sub_staircase t hanti).1 i)
  obtain ⟨q, hq, hqt⟩ := strictAnti_eq_shiftedPartition t hanti
    (n := (∑ i, t i) - staircaseDegree m) (by omega)
  have hlenp : length (transpose p) ≤ m := by rw [length_transpose_eq_width]; exact hp
  have hrows (i : ℕ) : rowLength q i ≤ rowLength (transpose p) i ∧
      rowLength (transpose p) i ≤ rowLength q i + 1 := by
    by_cases hi : i < m
    · have hh := ht ⟨i, hi⟩
      rw [← hqt] at hh
      change rowLength q i + _ ≤ rowLength (transpose p) i + _ ∧
        rowLength (transpose p) i + _ ≤ rowLength q i + _ + 1 at hh
      omega
    · rw [rowLength_zero_of_length_le q i (by omega),
        rowLength_zero_of_length_le (transpose p) i (by omega)]
      omega
  have hsub : diagram q ≤ diagram (transpose p) := by
    intro c hc
    apply YoungDiagram.mem_iff_lt_rowLen.mpr
    exact (YoungDiagram.mem_iff_lt_rowLen.mp hc).trans_le (hrows c.1).1
  let D := (diagram q).transpose
  have hDP : D ≤ diagram p := by
    have hh := YoungDiagram.transpose_mono hsub
    rwa [transpose_diagram, YoungDiagram.transpose_transpose] at hh
  have hstrip : ∀ i, (diagram p).rowLen (i+1) ≤ D.rowLen i := by
    apply (horizontalStrip_iff_column_bounds D (diagram p)).mpr
    intro j
    have hh := (hrows j).2
    rw [transpose_rowLength] at hh
    change (diagram p).colLen j ≤ (diagram q).rowLen j + 1 at hh
    simpa only [D, YoungDiagram.colLen_transpose] using hh
  let d : HorizontalSubshape p := ⟨D, hDP, hstrip⟩
  refine ⟨d, ?_⟩
  have hd : diagram (transpose (subshapePartition d)) = diagram q := by
    rw [transpose_diagram, diagram_subshapePartition]
    exact YoungDiagram.transpose_transpose _
  exact (shiftedPartition_eq_of_diagram_eq _ _ hd).trans hqt

/-- The elementary determinant has the same horizontal-strip branching as
semistandard tableaux of the original shape. -/
theorem dualJacobiTrudi_succ_alphabet {n m : ℕ} (p : Partition n) (r : ℕ)
    (hp : rowLength p 0 ≤ m) :
    dualJacobiTrudi p (r+1) m =
      ∑ d : HorizontalSubshape p,
        MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r+1))
          (dualJacobiTrudi (subshapePartition d) r m) *
          (MvPolynomial.X (Fin.last r) : Alphabet (r+1)) ^ (n-d.val.card) := by
  let b := shiftedPartition m (transpose p)
  let B := (Fintype.piFinset (fun i => Finset.Icc (b i-1) (b i))).filter StrictAnti
  have hmem (t : Fin m → ℕ) : t ∈ B ↔ EVectorBounded b t ∧ StrictAnti t := by
    simp only [B, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc, EVectorBounded]
    constructor
    · rintro ⟨ht, ha⟩
      exact ⟨fun i => ⟨(ht i).2, by have := (ht i).1; omega⟩, ha⟩
    · rintro ⟨ht, ha⟩
      exact ⟨fun i => ⟨by have := (ht i).2; omega, (ht i).1⟩, ha⟩
  let f : HorizontalSubshape p → B := fun d =>
    ⟨shiftedPartition m (transpose (subshapePartition d)),
      (hmem _).mpr ⟨subshape_transpose_shifted_mem p d, shiftedPartition_strictAnti _⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro d e he
      apply Subtype.ext
      have hh := diagram_eq_of_shiftedPartition_eq
        (transpose (subshapePartition d)) (transpose (subshapePartition e))
        (by rw [length_transpose_eq_width]; exact (subshape_width_le d).trans hp)
        (by rw [length_transpose_eq_width]; exact (subshape_width_le e).trans hp)
        (congrArg Subtype.val he)
      rw [transpose_diagram, transpose_diagram, diagram_subshapePartition,
        diagram_subshapePartition] at hh
      exact YoungDiagram.transpose_eq_iff.mp hh
    · rintro ⟨t, ht⟩
      obtain ⟨d, hd⟩ := exists_subshape_of_elementary_vector p hp t
        ((hmem t).mp ht).1 ((hmem t).mp ht).2
      exact ⟨d, Subtype.ext hd⟩
  let equiv := Equiv.ofBijective f hf
  rw [← shiftedEDet_shiftedPartition p, shiftedEDet_succ_strict r b
    (shiftedPartition_strictAnti (transpose p)), ← Finset.sum_coe_sort]
  symm
  apply Fintype.sum_equiv equiv
  intro d
  change _ = MvPolynomial.rename Fin.castSucc
    (shiftedEDet r (shiftedPartition m (transpose (subshapePartition d)))) *
      MvPolynomial.X (Fin.last r) ^ ((∑ i, shiftedPartition m (transpose p) i) -
        ∑ i, shiftedPartition m (transpose (subshapePartition d)) i)
  rw [shiftedEDet_shiftedPartition, sum_shiftedPartition (transpose p)
    (by rw [length_transpose_eq_width]; exact hp),
    sum_shiftedPartition (transpose (subshapePartition d))
      (by rw [length_transpose_eq_width]; exact (subshape_width_le d).trans hp),
    Nat.add_sub_add_right]

/-- Alphabet induction, starting at the empty alphabet. -/
theorem dualJacobiTrudi_eq_tableauSum {n : ℕ} (p : Partition n) (r q : ℕ)
    (hq : rowLength p 0 ≤ q) : dualJacobiTrudi p r q = tableauSum p r := by
  induction r generalizing n with
  | zero => rw [dualJacobiTrudi_no_variables p q hq, tableauSum_no_variables]
  | succ r ih =>
    rw [dualJacobiTrudi_succ_alphabet p r hq, tableauSum_succ_alphabet p r]
    apply Finset.sum_congr rfl
    intro d _
    rw [ih (subshapePartition d) ((subshape_width_le d).trans hq)]

/-- Dual Jacobi–Trudi for every finite alphabet and every adequate padding. -/
theorem dual_jacobi_trudi {n : ℕ} (p : Partition n) (r q : ℕ)
    (hq : rowLength p 0 ≤ q) : schurPolynomial p r = dualJacobiTrudi p r q := by
  rw [dualJacobiTrudi_eq_tableauSum p r q hq, schurPolynomial_eq_tableauSum]

end AdvancedFiniteGroupRepresentations
