import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.SchurAlternant
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SchurTableauFormula
import Mathlib.LinearAlgebra.Matrix.Adjugate

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Matrix
open Classical
namespace AdvancedFiniteGroupRepresentations

abbrev paddedJacobiTrudiMatrix :=
  @Specs.AdvancedFiniteGroupRepresentations.paddedJacobiTrudiMatrix
abbrev paddedJacobiTrudi := @Specs.AdvancedFiniteGroupRepresentations.paddedJacobiTrudi

theorem paddedJacobiTrudi_same_size {n : ℕ} (p : Partition n) (r : ℕ) :
    paddedJacobiTrudi p r r = jacobiTrudi p r := rfl

/-- Adding a zero row to the shape adds a final matrix row `(0,...,0,1)`. -/
theorem paddedJacobiTrudi_succ {n : ℕ} (p : Partition n) (r m : ℕ)
    (hp : length p ≤ m) :
    paddedJacobiTrudi p r (m + 1) = paddedJacobiTrudi p r m := by
  classical
  let A := paddedJacobiTrudiMatrix p r (m + 1)
  have hrow : rowLength p m = 0 := rowLength_zero_of_length_le p m hp
  have hlast : A (Fin.last m) (Fin.last m) = 1 := by
    change h r ((rowLength p m : ℤ) - (m : ℤ) + (m : ℤ)) = 1
    simpa only [hrow, Nat.cast_zero, zero_sub, neg_add_cancel] using h_zero r
  have hzero (j : Fin m) : A (Fin.last m) j.castSucc = 0 := by
    change h r ((rowLength p m : ℤ) - (m : ℤ) + (j.val : ℤ)) = 0
    rw [hrow]
    apply h_neg
    have hj := j.isLt
    omega
  have hminor : A.submatrix Fin.castSucc Fin.castSucc = paddedJacobiTrudiMatrix p r m := rfl
  change A.det = _
  rw [Matrix.det_succ_row A (Fin.last m), Fin.sum_univ_castSucc]
  simp only [Fin.val_last, Fin.succAbove_last, hlast, hzero, mul_zero, zero_mul,
    Finset.sum_const_zero, zero_add, mul_one, hminor]
  rw [← two_mul, pow_mul]
  simp
  rfl

theorem paddedJacobiTrudi_stable {n : ℕ} (p : Partition n) (r m k : ℕ)
    (hp : length p ≤ m) (hmk : m ≤ k) :
    paddedJacobiTrudi p r k = paddedJacobiTrudi p r m := by
  induction k, hmk using Nat.le_induction with
  | base => rfl
  | @succ k hmk ih =>
    rw [paddedJacobiTrudi_succ p r k (hp.trans hmk), ih]

/-- Row padding does not require padding the alphabet. -/
theorem paddedJacobiTrudi_eq_schurPolynomial_of_length_le {n : ℕ}
    (p : Partition n) (r m : ℕ) (hm : length p ≤ m) (hr : length p ≤ r) :
    paddedJacobiTrudi p r m = schurPolynomial p r := by
  calc
    paddedJacobiTrudi p r m = paddedJacobiTrudi p r (max m r) :=
      (paddedJacobiTrudi_stable p r m (max m r) hm (le_max_left m r)).symm
    _ = paddedJacobiTrudi p r r :=
      paddedJacobiTrudi_stable p r r (max m r) hr (le_max_right m r)
    _ = schurPolynomial p r := (schurPolynomial_eq_jacobiTrudi p r hr).symm

theorem empty_paddedJacobiTrudi (r m : ℕ) :
    paddedJacobiTrudi emptyPartition r m = 1 := by
  rw [paddedJacobiTrudi_stable emptyPartition r 0 m (by rw [empty_length]) (Nat.zero_le m)]
  exact Matrix.det_isEmpty

/-- A nonempty partition has a positive first row. -/
theorem rowLength_zero_pos_of_size_pos {n : ℕ} (p : Partition n) (hn : 0 < n) :
    0 < rowLength p 0 := by
  by_contra hp
  have hz : rowLength p 0 = 0 := by omega
  have hall : ∀ i, rowLength p i = 0 := by
    intro i
    have hi := rowLength_antitone p (Nat.zero_le i)
    omega
  have hc : cells p = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    have hh := (cell_iff p c.1 c.2).mp hc
    rw [hall c.1] at hh
    omega
  have he : (diagram p).card = 0 := by
    change (cells p).card = 0
    rw [hc, Finset.card_empty]
  have hs := diagram_card p
  omega

theorem paddedJacobiTrudi_no_variables {n : ℕ} (p : Partition n) (m : ℕ)
    (hp : length p ≤ m) :
    paddedJacobiTrudi p 0 m = if n = 0 then 1 else 0 := by
  classical
  split_ifs with hn
  · subst n
    rw [zero_partition_unique p, empty_paddedJacobiTrudi]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hfirst := rowLength_zero_pos_of_size_pos p hnpos
    have hm : 0 < m := by
      by_contra hm
      have hlen : length p = 0 := by omega
      have hz := rowLength_zero_of_length_le p 0 (by omega)
      omega
    apply Matrix.det_eq_zero_of_row_eq_zero ⟨0, hm⟩
    intro j
    change h 0 ((rowLength p 0 : ℤ) - (0 : ℤ) + (j.val : ℤ)) = 0
    apply h_no_variables
    omega

theorem tableauSum_no_variables {n : ℕ} (p : Partition n) :
    tableauSum p 0 = if n = 0 then 1 else 0 := by
  split_ifs with hn
  · subst n
    rw [zero_partition_unique p, empty_tableauSum]
  · apply tableauSum_eq_zero_of_length_gt
    by_contra hp
    have hz : length p = 0 := by omega
    have he : parts p = [] := List.length_eq_zero_iff.mp hz
    have hs := parts_sum p
    rw [he, List.sum_nil] at hs
    exact hn hs.symm

theorem empty_schur_three_formulas (r m : ℕ) :
    schurPolynomial emptyPartition r = 1 ∧
    paddedJacobiTrudi emptyPartition r m = 1 ∧ tableauSum emptyPartition r = 1 :=
  ⟨empty_schurPolynomial r, empty_paddedJacobiTrudi r m, empty_tableauSum r⟩


/-- The finite denominator of the complete homogeneous generating series. -/
def hDenominator (r : ℕ) : Polynomial (Alphabet r) :=
  ∏ i : Fin r, (1 - Polynomial.C (MvPolynomial.X i) * Polynomial.X)

theorem hDenominator_coeff_zero (r : ℕ) : (hDenominator r).coeff 0 = 1 := by
  classical
  simp [hDenominator, Polynomial.coeff_zero_prod]

theorem hDenominator_natDegree_le (r : ℕ) : (hDenominator r).natDegree ≤ r := by
  classical
  calc
    _ ≤ ∑ i : Fin r, (1 - Polynomial.C (MvPolynomial.X i) * Polynomial.X :
        Polynomial (Alphabet r)).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i : Fin r, 1 := by
      apply Finset.sum_le_sum
      intro i _
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · simp
      · simp
    _ = r := by simp

theorem hDenominator_mul_hGeneratingSeries (r : ℕ) :
    (hDenominator r : PowerSeries (Alphabet r)) * hGeneratingSeries r = 1 := by
  classical
  rw [hGeneratingSeries_eq_product]
  change Polynomial.coeToPowerSeries.ringHom (hDenominator r) * _ = _
  simp only [hDenominator, map_prod, map_sub, map_one, map_mul,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  exact one_sub_mul_geometricSeries (MvPolynomial.X i : Alphabet r)

/-- The recurrence written with the stipulated zero values at negative indices. -/
theorem hDenominator_recurrence (r m k : ℕ) (hm : r < m) (hk : 0 < k) :
    (∑ s ∈ Finset.range m, (hDenominator r).coeff s * h r ((k : ℤ) - s)) = 0 := by
  classical
  let f : ℕ → Alphabet r := fun s => (hDenominator r).coeff s * h r ((k : ℤ) - s)
  have hcoeff (s : ℕ) (hs : r < s) : (hDenominator r).coeff s = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((hDenominator_natDegree_le r).trans_lt hs)
  have hsum : (∑ s ∈ Finset.range m, f s) = ∑ s ∈ Finset.range (k + 1), f s := by
    apply (Finset.sum_subset (Finset.range_mono (le_max_left m (k + 1))) ?_).trans
      (Finset.sum_subset (Finset.range_mono (le_max_right m (k + 1))) ?_).symm
    · intro s _ hs
      have hs' : m ≤ s := by simpa using hs
      simp [f, hcoeff s (by omega)]
    · intro s _ hs
      have hs' : k + 1 ≤ s := by simpa using hs
      dsimp [f]
      rw [h_neg r ((k : ℤ) - s) (by omega), mul_zero]
  have he := congrArg (PowerSeries.coeff k) (hDenominator_mul_hGeneratingSeries r)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a (hDenominator r : PowerSeries (Alphabet r)) *
      PowerSeries.coeff b (hGeneratingSeries r)) k] at he
  simp only [Polynomial.coeff_coe, hGeneratingSeries, PowerSeries.coeff_mk,
    PowerSeries.coeff_one, Nat.ne_of_gt hk, ite_false, Nat.succ_eq_add_one] at he
  change (∑ s ∈ Finset.range m, f s) = 0
  rw [hsum]
  convert he using 1
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hs)
  dsimp [f]
  rw [Int.ofNat_sub hs']

/-- Every row before the length is nonempty. -/
theorem rowLength_pos_of_lt_length {n : ℕ} (p : Partition n) (i : ℕ)
    (hi : i < length p) : 0 < rowLength p i := by
  apply (cell_iff p i 0).mp
  apply (cell_iff_column p i 0).mpr
  rwa [← length_eq_columnLength_zero]

theorem paddedJacobiTrudi_eq_zero_of_length_gt {n r : ℕ} (p : Partition n)
    (m : ℕ) (hm : length p ≤ m) (hr : r < length p) :
    paddedJacobiTrudi p r m = 0 := by
  classical
  rw [paddedJacobiTrudi_stable p r (length p) m le_rfl hm]
  let l := length p
  have hl : 0 < l := by dsimp [l]; omega
  let v : Fin l → Alphabet r := fun j => (hDenominator r).coeff (l - 1 - j.val)
  let A := paddedJacobiTrudiMatrix p r l
  have hv : v ⟨l - 1, by omega⟩ = 1 := by
    dsimp [v]
    rw [Nat.sub_self, hDenominator_coeff_zero]
  have hAv : A *ᵥ v = 0 := by
    funext i
    change (∑ j : Fin l, h r ((rowLength p i.val : ℤ) - i.val + j.val) *
      (hDenominator r).coeff (l - 1 - j.val)) = 0
    rw [← Equiv.sum_comp Fin.revPerm]
    simp only [Fin.revPerm_apply, Fin.val_rev]
    have hi := i.isLt
    have hp := rowLength_pos_of_lt_length p i.val hi
    let k := rowLength p i.val + (l - 1 - i.val)
    have he (j : Fin l) :
        h r ((rowLength p i.val : ℤ) - i.val + (l - (j.val + 1) : ℕ)) *
          (hDenominator r).coeff (l - 1 - (l - (j.val + 1))) =
        (hDenominator r).coeff j.val * h r ((k : ℤ) - j.val) := by
      have hj := j.isLt
      rw [show l - 1 - (l - (j.val + 1)) = j.val by omega, mul_comm]
      congr 2
      dsimp [k]
      omega
    simp_rw [he]
    rw [Fin.sum_univ_eq_sum_range
      (fun s : ℕ => (hDenominator r).coeff s * h r ((k : ℤ) - s)) l]
    exact hDenominator_recurrence r l k hr (by dsimp [k]; omega)
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hAv
  rw [hv]
  exact one_mem _

theorem paddedJacobiTrudi_eq_schurPolynomial {n : ℕ} (p : Partition n)
    (r m : ℕ) (hm : length p ≤ m) :
    paddedJacobiTrudi p r m = schurPolynomial p r := by
  by_cases hr : length p ≤ r
  · exact paddedJacobiTrudi_eq_schurPolynomial_of_length_le p r m hm hr
  · have hr' := Nat.lt_of_not_ge hr
    rw [paddedJacobiTrudi_eq_zero_of_length_gt p m hm hr',
      schurPolynomial_eq_zero_of_length_gt p hr']

theorem schur_length_cutoff {n r : ℕ} (p : Partition n) (m : ℕ)
    (hm : length p ≤ m) (hr : r < length p) :
    schurPolynomial p r = 0 ∧ paddedJacobiTrudi p r m = 0 ∧ tableauSum p r = 0 :=
  ⟨schurPolynomial_eq_zero_of_length_gt p hr,
    paddedJacobiTrudi_eq_zero_of_length_gt p m hm hr,
    tableauSum_eq_zero_of_length_gt hr⟩


/-- Separate the last geometric factor, retaining the actual finite alphabets. -/
theorem hGeneratingSeries_succ (r : ℕ) :
    hGeneratingSeries (r + 1) =
      PowerSeries.map (MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r + 1))).toRingHom
        (hGeneratingSeries r) * variableGeometricSeries (Fin.last r) := by
  classical
  rw [hGeneratingSeries_eq_product, hGeneratingSeries_eq_product, map_prod,
    Fin.prod_univ_castSucc]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  apply PowerSeries.ext
  intro k
  simp [variableGeometricSeries, PowerSeries.coeff_map]

theorem h_succ_alphabet (r k : ℕ) :
    h (r + 1) (k : ℤ) = ∑ a ∈ Finset.range (k + 1),
      MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r + 1)) (h r ((k - a : ℕ) : ℤ)) *
        (MvPolynomial.X (Fin.last r) : Alphabet (r + 1)) ^ a := by
  have he := congrArg (PowerSeries.coeff k) (hGeneratingSeries_succ r)
  rw [mul_comm, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a (variableGeometricSeries (Fin.last r)) *
        PowerSeries.coeff b (PowerSeries.map
          (MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r + 1))).toRingHom
          (hGeneratingSeries r))) k] at he
  simpa only [hGeneratingSeries, PowerSeries.coeff_mk, PowerSeries.coeff_map,
    variableGeometricSeries, Nat.succ_eq_add_one, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, mul_comm] using he

/-- A finite integer-index version convenient for expanding determinant rows. -/
theorem h_succ_alphabet_shift (r b d : ℕ) :
    h (r + 1) ((b : ℤ) - d) = ∑ t ∈ Finset.range (b + 1),
      MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r + 1)) (h r ((t : ℤ) - d)) *
        (MvPolynomial.X (Fin.last r) : Alphabet (r + 1)) ^ (b - t) := by
  classical
  by_cases hbd : d ≤ b
  · rw [← Int.ofNat_sub hbd, h_succ_alphabet]
    have hshift : (∑ a ∈ Finset.range (b - d + 1),
        MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r + 1))
          (h r ((b - d - a : ℕ) : ℤ)) *
        (MvPolynomial.X (Fin.last r) : Alphabet (r + 1)) ^ a) =
      ∑ a ∈ Finset.range (b + 1),
        MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r + 1))
          (h r ((b : ℤ) - d - a)) *
        (MvPolynomial.X (Fin.last r) : Alphabet (r + 1)) ^ a := by
      calc
        _ = ∑ a ∈ Finset.range (b - d + 1),
            MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r + 1))
              (h r ((b : ℤ) - d - a)) *
            (MvPolynomial.X (Fin.last r) : Alphabet (r + 1)) ^ a := by
          apply Finset.sum_congr rfl
          intro a ha
          congr 3
          have ha := Finset.mem_range.mp ha
          omega
        _ = _ := by
          apply Finset.sum_subset (Finset.range_mono (by omega))
          intro a _ ha
          have ha : b - d + 1 ≤ a := by simpa using ha
          rw [h_neg r _ (by omega), map_zero, zero_mul]
    rw [hshift]
    conv_rhs => rw [← Finset.sum_range_reflect
      (fun t => MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r + 1))
        (h r ((t : ℤ) - d)) *
        (MvPolynomial.X (Fin.last r) : Alphabet (r + 1)) ^ (b - t)) (b + 1)]
    apply Finset.sum_congr rfl
    intro a ha
    have ha := Finset.mem_range.mp ha
    have hb : b + 1 - 1 - a = b - a := by omega
    rw [hb, show b - (b - a) = a by omega]
    congr 3
    omega
  · rw [h_neg (r + 1) _ (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro t ht
    have ht := Finset.mem_range.mp ht
    rw [h_neg r _ (by omega), map_zero, zero_mul]

/-- Determinant with an arbitrary nonnegative shifted exponent vector. -/
def shiftedHDet (r : ℕ) {m : ℕ} (b : Fin m → ℕ) : Alphabet r :=
  (Matrix.of fun i j : Fin m => h r ((b i : ℤ) - (staircase m j : ℤ))).det

/-- Expansion before the mirror involution cancels noninterlacing vectors. -/
theorem shiftedHDet_succ_expansion (r : ℕ) {m : ℕ} (b : Fin m → ℕ) :
    shiftedHDet (r + 1) b =
      ∑ t ∈ Fintype.piFinset (fun i => Finset.range (b i + 1)),
        MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r + 1)) (shiftedHDet r t) *
          (MvPolynomial.X (Fin.last r) : Alphabet (r + 1)) ^ ((∑ i, b i) - ∑ i, t i) := by
  classical
  let z : Alphabet (r + 1) := MvPolynomial.X (Fin.last r)
  let ι : Alphabet r →ₐ[ℂ] Alphabet (r + 1) := MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r + 1))
  let g : Fin m → ℕ → (Fin m → Alphabet (r + 1)) :=
    fun i t j => z ^ (b i - t) * ι (h r ((t : ℤ) - (staircase m j : ℤ)))
  have he : (Matrix.of fun i j : Fin m =>
      h (r + 1) ((b i : ℤ) - (staircase m j : ℤ))) =
      fun i => ∑ t ∈ Finset.range (b i + 1), g i t := by
    funext i j
    simp only [Matrix.of_apply, Finset.sum_apply, g]
    rw [h_succ_alphabet_shift]
    apply Finset.sum_congr rfl
    intro t _
    exact mul_comm _ _
  change Matrix.det _ = _
  rw [he]
  have hm := Matrix.detRowAlternating.toMultilinearMap.map_sum_finset g
    (fun i => Finset.range (b i + 1))
  change Matrix.det _ = _ at hm
  rw [hm]
  apply Finset.sum_congr rfl
  intro t ht
  have ht : ∀ i, t i ≤ b i := by
    intro i
    exact Nat.le_of_lt_succ (Finset.mem_range.mp (Fintype.mem_piFinset.mp ht i))
  change (Matrix.of fun i j => z ^ (b i - t i) * ι (h r ((t i : ℤ) - (staircase m j : ℤ)))).det = _
  erw [Matrix.det_mul_column (fun i => z ^ (b i - t i))
    (Matrix.of fun i j => ι (h r ((t i : ℤ) - (staircase m j : ℤ)))), Finset.prod_pow_eq_pow_sum, Finset.sum_tsub_distrib _ (fun i _ => ht i)]
  rw [mul_comm]
  congr 1
  change _ = ι.toRingHom (Matrix.of fun i j : Fin m => h r ((t i : ℤ) - (staircase m j : ℤ))).det
  rw [RingHom.map_det]
  rfl

theorem shiftedHDet_comp_swap (r : ℕ) {m : ℕ} (t : Fin m → ℕ)
    (i j : Fin m) (hij : i ≠ j) :
    shiftedHDet r (t ∘ Equiv.swap i j) = -shiftedHDet r t := by
  change ((Matrix.of fun i j : Fin m => h r ((t i : ℤ) - (staircase m j : ℤ))).submatrix
    (Equiv.swap i j) id).det = _
  rw [Matrix.det_permute, Equiv.Perm.sign_swap hij]
  simp [shiftedHDet]

/-- Bounds for the finite vector expansion. -/
def HVectorBounded {m : ℕ} (b t : Fin m → ℕ) : Prop := ∀ i, t i ≤ b i

/-- Adjacent inequalities that characterize the surviving exponent vectors. -/
def HVectorInterlaces {m : ℕ} (b t : Fin (m + 1) → ℕ) : Prop :=
  ∀ i : Fin m, b i.succ < t i.castSucc

private def hBadIndices {m : ℕ} (b t : Fin (m + 1) → ℕ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => t i.castSucc ≤ b i.succ)

private theorem mem_hBadIndices {m : ℕ} (b t : Fin (m + 1) → ℕ) (i : Fin m) :
    i ∈ hBadIndices b t ↔ t i.castSucc ≤ b i.succ := by
  classical
  simp [hBadIndices]

private theorem hBadIndices_nonempty {m : ℕ} (b t : Fin (m + 1) → ℕ) :
    (hBadIndices b t).Nonempty ↔ ¬ HVectorInterlaces b t := by
  classical
  simp only [HVectorInterlaces, not_forall, not_lt]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (mem_hBadIndices b t i).mp hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (mem_hBadIndices b t i).mpr hi⟩

private def hMirror {m : ℕ} (b t : Fin (m + 1) → ℕ) : Fin (m + 1) → ℕ := by
  classical
  exact if H : (hBadIndices b t).Nonempty then
    t ∘ Equiv.swap ((hBadIndices b t).min' H).castSucc ((hBadIndices b t).min' H).succ
    else t

private theorem hMirror_facts {m : ℕ} (b t : Fin (m + 1) → ℕ)
    (hb : Antitone b) (ht : HVectorBounded b t) (H : (hBadIndices b t).Nonempty) :
    HVectorBounded b (hMirror b t) ∧
    (hBadIndices b (hMirror b t)).Nonempty ∧
    ∀ H' : (hBadIndices b (hMirror b t)).Nonempty,
      (hBadIndices b (hMirror b t)).min' H' = (hBadIndices b t).min' H := by
  classical
  let i := (hBadIndices b t).min' H
  have hi : t i.castSucc ≤ b i.succ :=
    (mem_hBadIndices b t i).mp (Finset.min'_mem _ H)
  have he : hMirror b t = t ∘ Equiv.swap i.castSucc i.succ := by
    simp only [hMirror, dite_eq_left H, i]
  have hne : i.castSucc ≠ i.succ := Fin.castSucc_lt_succ.ne
  have hbound : HVectorBounded b (hMirror b t) := by
    intro j
    rw [he]
    simp only [Function.comp_apply]
    by_cases hji : j = i.castSucc
    · subst j
      rw [Equiv.swap_apply_left]
      exact (ht i.succ).trans (hb Fin.castSucc_lt_succ.le)
    · by_cases hjs : j = i.succ
      · subst j
        rw [Equiv.swap_apply_right]
        exact hi
      · rw [Equiv.swap_apply_of_ne_of_ne hji hjs]
        exact ht j
  have hmem : i ∈ hBadIndices b (hMirror b t) := by
    rw [mem_hBadIndices, he, Function.comp_apply, Equiv.swap_apply_left]
    exact ht i.succ
  refine ⟨hbound, ⟨i, hmem⟩, ?_⟩
  intro H'
  apply (Finset.min'_eq_iff _ _ _).mpr
  refine ⟨hmem, ?_⟩
  intro j hj
  by_contra hij
  have hji : j < i := lt_of_not_ge hij
  have h₁ : j.castSucc ≠ i.castSucc := fun h => hji.ne (Fin.castSucc_injective _ h)
  have h₂ : j.castSucc ≠ i.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    have hv' : j.val < i.val := hji
    omega
  have hj' : j ∈ hBadIndices b t := by
    rw [mem_hBadIndices] at hj ⊢
    rw [he, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h₁ h₂] at hj
    exact hj
  exact (not_lt_of_ge (Finset.min'_le _ j hj')) hji

private theorem hMirror_involutive {m : ℕ} (b t : Fin (m + 1) → ℕ)
    (hb : Antitone b) (ht : HVectorBounded b t) (H : (hBadIndices b t).Nonempty) :
    hMirror b (hMirror b t) = t := by
  classical
  obtain ⟨_, H', he⟩ := hMirror_facts b t hb ht H
  rw [hMirror, dite_eq_left H', he H']
  rw [hMirror, dite_eq_left H]
  funext i
  simp

/-- Mirror cancellation leaves exactly the interlacing exponent vectors. -/
theorem shiftedHDet_succ_interlacing (r : ℕ) {m : ℕ} (b : Fin (m + 1) → ℕ)
    (hb : Antitone b) :
    shiftedHDet (r + 1) b =
      ∑ t ∈ (Fintype.piFinset (fun i => Finset.range (b i + 1))).filter
        (HVectorInterlaces b),
        MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r + 1)) (shiftedHDet r t) *
          (MvPolynomial.X (Fin.last r) : Alphabet (r + 1)) ^ ((∑ i, b i) - ∑ i, t i) := by
  classical
  let B := Fintype.piFinset (fun i => Finset.range (b i + 1))
  let f : (Fin (m + 1) → ℕ) → Alphabet (r + 1) := fun t =>
    MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r + 1)) (shiftedHDet r t) *
      (MvPolynomial.X (Fin.last r) : Alphabet (r + 1)) ^ ((∑ i, b i) - ∑ i, t i)
  have hB (t : Fin (m + 1) → ℕ) : t ∈ B ↔ HVectorBounded b t := by
    simp only [B, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff, HVectorBounded]
  let bad := B.filter (fun t => ¬ HVectorInterlaces b t)
  have hsign (t) (ht : t ∈ bad) : f (hMirror b t) = -f t := by
    have H := (hBadIndices_nonempty b t).mpr (Finset.mem_filter.mp ht).2
    let i := (hBadIndices b t).min' H
    have he : hMirror b t = t ∘ Equiv.swap i.castSucc i.succ := by
      simp only [hMirror, dite_eq_left H, i]
    have hs : (∑ j, hMirror b t j) = ∑ j, t j := by
      rw [he]
      exact Equiv.sum_comp (Equiv.swap i.castSucc i.succ) t
    dsimp only [f]
    rw [hs, he, shiftedHDet_comp_swap r t _ _ Fin.castSucc_lt_succ.ne, map_neg, neg_mul]
  have hmem (t) (ht : t ∈ bad) : hMirror b t ∈ bad := by
    obtain ⟨htB, htI⟩ := Finset.mem_filter.mp ht
    have H := (hBadIndices_nonempty b t).mpr htI
    obtain ⟨hbound, H', _⟩ := hMirror_facts b t hb ((hB t).mp htB) H
    exact Finset.mem_filter.mpr ⟨(hB _).mpr hbound, (hBadIndices_nonempty _ _).mp H'⟩
  have hcancel : (∑ t ∈ bad, f t) = 0 := by
    apply Finset.sum_involution (fun t _ => hMirror b t)
    · intro t ht
      rw [hsign t ht, add_neg_cancel]
    · intro t ht hn he
      have hz : (2 : Alphabet (r + 1)) * f t = 0 := by
        rw [two_mul]
        have hh := hsign t ht
        rw [he] at hh
        calc
          f t + f t = f t + -f t := congrArg (fun x => f t + x) hh
          _ = 0 := add_neg_cancel _
      exact hn ((mul_eq_zero.mp hz).resolve_left (by norm_num))
    · exact hmem
    · intro t ht
      obtain ⟨htB, htI⟩ := Finset.mem_filter.mp ht
      exact hMirror_involutive b t hb ((hB t).mp htB) ((hBadIndices_nonempty b t).mpr htI)
  rw [shiftedHDet_succ_expansion]
  change (∑ t ∈ B, f t) = _
  have he := Finset.sum_filter_add_sum_filter_not B (HVectorInterlaces b) f
  rw [show (∑ t ∈ B with ¬ HVectorInterlaces b t, f t) = 0 from hcancel, add_zero] at he
  exact he.symm


/-- Remove a horizontal strip, including the empty strip. -/
def HorizontalSubshape {n : ℕ} (p : Partition n) :=
  {d : YoungDiagram // d ≤ diagram p ∧ ∀ i, rowLength p (i + 1) ≤ d.rowLen i}

instance {n : ℕ} (p : Partition n) : Finite (HorizontalSubshape p) := by
  let f : HorizontalSubshape p → ((cells p).powerset : Finset (Finset (ℕ × ℕ))) :=
    fun d => ⟨d.val.cells, Finset.mem_powerset.mpr d.property.1⟩
  apply Finite.of_injective f
  intro a b h
  apply Subtype.ext
  apply YoungDiagram.ext
  exact congrArg Subtype.val h

noncomputable instance {n : ℕ} (p : Partition n) : Fintype (HorizontalSubshape p) :=
  Fintype.ofFinite _

/-- The canonical partition of a subdiagram, with its actual number of cells. -/
def subshapePartition {n : ℕ} {p : Partition n} (d : HorizontalSubshape p) :
    Partition d.val.card := d.val.toPartition rfl

@[simp] theorem diagram_subshapePartition {n : ℕ} {p : Partition n}
    (d : HorizontalSubshape p) : diagram (subshapePartition d) = d.val :=
  YoungDiagram.ofPartition_toPartition _

theorem subshape_card_le {n : ℕ} {p : Partition n} (d : HorizontalSubshape p) :
    d.val.card ≤ n := by
  calc
    _ ≤ (diagram p).card := Finset.card_le_card d.property.1
    _ = n := diagram_card p

theorem subshape_length_le {n : ℕ} {p : Partition n} (d : HorizontalSubshape p) :
    length (subshapePartition d) ≤ length p := by
  rw [length_eq_columnLength_zero, length_eq_columnLength_zero]
  change (diagram (subshapePartition d)).colLen 0 ≤ (diagram p).colLen 0
  rw [diagram_subshapePartition]
  by_contra h
  have hc : ((diagram p).colLen 0, 0) ∈ d.val :=
    YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  have hc := d.property.1 hc
  have := YoungDiagram.mem_iff_lt_colLen.mp hc
  omega

theorem shiftedHDet_shiftedPartition {n : ℕ} (p : Partition n) (r m : ℕ) :
    shiftedHDet r (shiftedPartition m p) = paddedJacobiTrudi p r m := by
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  change h r _ = h r _
  congr 1
  have hi := i.isLt
  have hj := j.isLt
  change ((rowLength p i.val + (m - 1 - i.val) : ℕ) : ℤ) -
    ((m - 1 - j.val : ℕ) : ℤ) = (rowLength p i.val : ℤ) - i.val + j.val
  omega

/-- Subshapes correspond to the surviving bounded shifted exponent vectors. -/
theorem subshape_shifted_mem {n m : ℕ} (p : Partition n) (hp : length p ≤ m + 1)
    (d : HorizontalSubshape p) :
    HVectorBounded (shiftedPartition (m + 1) p) (shiftedPartition (m + 1) (subshapePartition d)) ∧
    HVectorInterlaces (shiftedPartition (m + 1) p)
      (shiftedPartition (m + 1) (subshapePartition d)) := by
  have hrows (i : ℕ) : rowLength (subshapePartition d) i ≤ rowLength p i := by
    change (diagram (subshapePartition d)).rowLen i ≤ _
    rw [diagram_subshapePartition]
    by_contra h
    have hc : (i, rowLength p i) ∈ d.val := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hc := d.property.1 hc
    exact (lt_irrefl (rowLength p i)) (YoungDiagram.mem_iff_lt_rowLen.mp hc)
  constructor
  · intro i
    exact Nat.add_le_add_right (hrows i.val) _
  · intro i
    have hs := d.property.2 i.val
    have hi := i.isLt
    change rowLength p (i.val + 1) + (m + 1 - 1 - (i.val + 1)) <
      (diagram (subshapePartition d)).rowLen i.val + (m + 1 - 1 - i.val)
    rw [diagram_subshapePartition]
    omega

/-- Construct the actual subdiagram from an uncancelled exponent vector. -/
theorem exists_subshape_of_interlaces {n m : ℕ} (p : Partition n) (hp : length p ≤ m + 1)
    (t : Fin (m + 1) → ℕ)
    (ht : HVectorBounded (shiftedPartition (m + 1) p) t)
    (hI : HVectorInterlaces (shiftedPartition (m + 1) p) t) :
    ∃ d : HorizontalSubshape p, shiftedPartition (m + 1) (subshapePartition d) = t := by
  have hanti : StrictAnti t := Fin.strictAnti_iff_succ_lt.mpr (fun i =>
    (ht i.succ).trans_lt (hI i))
  have htdeg : staircaseDegree (m + 1) ≤ ∑ i, t i := by
    exact Finset.sum_le_sum (fun i _ => (strictAnti_sub_staircase t hanti).1 i)
  obtain ⟨q, hq, hqt⟩ := strictAnti_eq_shiftedPartition t hanti
    (n := (∑ i, t i) - staircaseDegree (m + 1)) (by omega)
  have hrows (i : ℕ) : rowLength q i ≤ rowLength p i := by
    by_cases hi : i < m + 1
    · have hh := ht ⟨i, hi⟩
      rw [← hqt] at hh
      exact Nat.le_of_add_le_add_right hh
    · rw [rowLength_zero_of_length_le q i (by omega)]
      exact Nat.zero_le _
  have hsub : diagram q ≤ diagram p := by
    intro c hc
    rcases c with ⟨i,j⟩
    apply YoungDiagram.mem_iff_lt_rowLen.mpr
    exact (YoungDiagram.mem_iff_lt_rowLen.mp hc).trans_le (hrows i)
  have hstrip (i : ℕ) : rowLength p (i + 1) ≤ (diagram q).rowLen i := by
    by_cases hi : i < m
    · have hh := hI ⟨i, hi⟩
      rw [← hqt] at hh
      change rowLength p (i + 1) + (m + 1 - 1 - (i + 1)) <
        rowLength q i + (m + 1 - 1 - i) at hh
      change rowLength p (i + 1) ≤ rowLength q i
      omega
    · rw [rowLength_zero_of_length_le p (i + 1) (by omega)]
      exact Nat.zero_le _
  let d : HorizontalSubshape p := ⟨diagram q, hsub, hstrip⟩
  refine ⟨d, ?_⟩
  rw [← shiftedPartition_eq_of_diagram_eq (subshapePartition d) q
    (diagram_subshapePartition d)] at hqt
  exact hqt

/-- The determinant branches by deleting one horizontal strip. -/
theorem paddedJacobiTrudi_succ_alphabet {n m : ℕ} (p : Partition n) (r : ℕ)
    (hp : length p ≤ m + 1) :
    paddedJacobiTrudi p (r + 1) (m + 1) =
      ∑ d : HorizontalSubshape p,
        MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r + 1))
          (paddedJacobiTrudi (subshapePartition d) r (m + 1)) *
          (MvPolynomial.X (Fin.last r) : Alphabet (r + 1)) ^ (n - d.val.card) := by
  classical
  let b := shiftedPartition (m + 1) p
  let B := (Fintype.piFinset (fun i => Finset.range (b i + 1))).filter (HVectorInterlaces b)
  have hmem (t : Fin (m + 1) → ℕ) : t ∈ B ↔ HVectorBounded b t ∧ HVectorInterlaces b t := by
    simp only [B, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
      Nat.lt_succ_iff, HVectorBounded]
  let f : HorizontalSubshape p → B := fun d =>
    ⟨shiftedPartition (m + 1) (subshapePartition d),
      (hmem _).mpr (subshape_shifted_mem p hp d)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro d e h
      apply Subtype.ext
      have he := diagram_eq_of_shiftedPartition_eq (subshapePartition d) (subshapePartition e)
        ((subshape_length_le d).trans hp) ((subshape_length_le e).trans hp)
        (congrArg Subtype.val h)
      simpa only [diagram_subshapePartition] using he
    · rintro ⟨t, ht⟩
      obtain ⟨d, hd⟩ := exists_subshape_of_interlaces p hp t ((hmem t).mp ht).1 ((hmem t).mp ht).2
      exact ⟨d, Subtype.ext hd⟩
  let e := Equiv.ofBijective f hf
  rw [← shiftedHDet_shiftedPartition p, shiftedHDet_succ_interlacing r b
    (shiftedPartition_strictAnti p).antitone, ← Finset.sum_coe_sort]
  symm
  apply Fintype.sum_equiv e
  intro d
  change _ = MvPolynomial.rename Fin.castSucc
    (shiftedHDet r (shiftedPartition (m + 1) (subshapePartition d))) *
      MvPolynomial.X (Fin.last r) ^
        ((∑ i, shiftedPartition (m + 1) p i) -
          ∑ i, shiftedPartition (m + 1) (subshapePartition d) i)
  rw [shiftedHDet_shiftedPartition,
    sum_shiftedPartition p hp, sum_shiftedPartition (subshapePartition d)
      ((subshape_length_le d).trans hp), Nat.add_sub_add_right]


/-- Semistandard entries are weakly increasing for the product order on cells. -/
theorem tableau_up_left_weak {n r : ℕ} {p : Partition n}
    (T : SemistandardFilling p r) (a b : Cell p)
    (hi : a.val.1 ≤ b.val.1) (hj : a.val.2 ≤ b.val.2) : T.val a ≤ T.val b := by
  let c : Cell p := ⟨(a.val.1, b.val.2), (diagram p).up_left_mem hi le_rfl b.property⟩
  have hac : T.val a ≤ T.val c := T.property.1 a c rfl hj
  by_cases h : a.val.1 = b.val.1
  · have hcb : c = b := Subtype.ext (Prod.ext h rfl)
    rwa [hcb] at hac
  · exact hac.trans (T.property.2 c b rfl (lt_of_le_of_ne hi h)).le

/-- Delete exactly the cells carrying the largest letter. -/
def trimmedDiagram {n r : ℕ} {p : Partition n} (T : SemistandardFilling p (r + 1)) :
    YoungDiagram where
  cells := (cells p).filter (fun c => ∀ hc : c ∈ cells p, (T.val ⟨c, hc⟩).val < r)
  isLowerSet := by
    intro b a hab hb
    obtain ⟨hbp, hbt⟩ := Finset.mem_filter.mp hb
    have hap : a ∈ cells p := (diagram p).isLowerSet hab hbp
    apply Finset.mem_filter.mpr
    refine ⟨hap, ?_⟩
    intro ha
    exact lt_of_le_of_lt (show (T.val ⟨a,ha⟩).val ≤ (T.val ⟨b,hbp⟩).val from
      tableau_up_left_weak T _ _ hab.1 hab.2) (hbt hbp)

@[simp] theorem mem_trimmedDiagram {n r : ℕ} {p : Partition n}
    (T : SemistandardFilling p (r + 1)) (c : Cell p) :
    c.val ∈ trimmedDiagram T ↔ (T.val c).val < r := by
  change c.val ∈ (trimmedDiagram T).cells ↔ _
  rw [trimmedDiagram, Finset.mem_filter]
  simp only [c.property, forall_true_left, true_and]

/-- The largest-letter cells form a horizontal strip. -/
def trimmedSubshape {n r : ℕ} {p : Partition n} (T : SemistandardFilling p (r + 1)) :
    HorizontalSubshape p := ⟨trimmedDiagram T, by
  constructor
  · intro c hc
    exact (Finset.mem_filter.mp hc).1
  · intro i
    by_contra h
    have hj : (trimmedDiagram T).rowLen i < rowLength p (i + 1) := by omega
    let b : Cell p := ⟨(i + 1, (trimmedDiagram T).rowLen i),
      YoungDiagram.mem_iff_lt_rowLen.mpr hj⟩
    let a : Cell p := ⟨(i, (trimmedDiagram T).rowLen i),
      (diagram p).up_left_mem (Nat.le_succ i) le_rfl b.property⟩
    have hab : T.val a < T.val b := T.property.2 a b rfl (Nat.lt_succ_self i)
    have ha : a.val ∈ trimmedDiagram T := (mem_trimmedDiagram T a).mpr (by
      have hb := (T.val b).isLt
      change (T.val a).val < (T.val b).val at hab
      omega)
    have := YoungDiagram.mem_iff_lt_rowLen.mp ha
    exact (lt_irrefl _) this⟩

@[simp] theorem mem_trimmedSubshape {n r : ℕ} {p : Partition n}
    (T : SemistandardFilling p (r + 1)) (c : Cell p) :
    c.val ∈ (trimmedSubshape T).val ↔ (T.val c).val < r := mem_trimmedDiagram T c

/-- Include a cell of the subshape in the original shape. -/
def subshapeCell {n : ℕ} {p : Partition n} (d : HorizontalSubshape p)
    (c : Cell (subshapePartition d)) : Cell p :=
  ⟨c.val, d.property.1 (by
    have hc : c.val ∈ diagram (subshapePartition d) := c.property
    rwa [diagram_subshapePartition] at hc)⟩

/-- Restrict a tableau after deleting its largest-letter cells. -/
def restrictTableau {n r : ℕ} {p : Partition n} (T : SemistandardFilling p (r + 1)) :
    SemistandardFilling (subshapePartition (trimmedSubshape T)) r :=
  ⟨fun c => ⟨(T.val (subshapeCell (trimmedSubshape T) c)).val, by
      apply (mem_trimmedSubshape T _).mp
      have hc : c.val ∈ diagram (subshapePartition (trimmedSubshape T)) := c.property
      rwa [diagram_subshapePartition] at hc⟩,
    by
      constructor
      · intro a b hi hj
        exact T.property.1 _ _ hi hj
      · intro a b hj hi
        exact T.property.2 _ _ hj hi⟩

/-- Fill a removed horizontal strip with the largest letter. -/
def extendTableau {n r : ℕ} {p : Partition n} (d : HorizontalSubshape p)
    (T : SemistandardFilling (subshapePartition d) r) : SemistandardFilling p (r + 1) :=
  ⟨fun c => if hc : c.val ∈ d.val then
    (T.val ⟨c.val, by change c.val ∈ diagram (subshapePartition d); rwa [diagram_subshapePartition]⟩).castSucc
    else Fin.last r,
    by
      constructor
      · intro a b hi hj
        by_cases hb : b.val ∈ d.val
        · have ha : a.val ∈ d.val := d.val.isLowerSet (Prod.mk_le_mk.mpr ⟨hi.le, hj⟩) hb
          simp only [dite_eq_left ha, dite_eq_left hb]
          exact T.property.1 _ _ hi hj
        · simp only [dite_eq_right hb]
          exact Fin.le_last _
      · intro a b hj hi
        have ha : a.val ∈ d.val := by
          apply YoungDiagram.mem_iff_lt_rowLen.mpr
          have hb := YoungDiagram.mem_iff_lt_rowLen.mp b.property
          have hp := (diagram p).rowLen_anti (a.val.1 + 1) b.val.1 (by omega)
          exact lt_of_lt_of_le (show a.val.2 < rowLength p (a.val.1 + 1) from
            lt_of_lt_of_le (hj ▸ hb) hp) (d.property.2 a.val.1)
        by_cases hb : b.val ∈ d.val
        · simp only [dite_eq_left ha, dite_eq_left hb]
          exact T.property.2 _ _ hj hi
        · simp only [dite_eq_left ha, dite_eq_right hb]
          exact Fin.castSucc_lt_last _⟩

@[simp] theorem trimmedSubshape_extendTableau {n r : ℕ} {p : Partition n}
    (d : HorizontalSubshape p) (T : SemistandardFilling (subshapePartition d) r) :
    trimmedSubshape (extendTableau d T) = d := by
  apply Subtype.ext
  apply YoungDiagram.ext
  ext c
  by_cases hp : c ∈ cells p
  · change c ∈ trimmedDiagram (extendTableau d T) ↔ c ∈ d.val
    have hh := mem_trimmedDiagram (extendTableau d T) (⟨c,hp⟩ : Cell p)
    change c ∈ trimmedDiagram (extendTableau d T) ↔ _ at hh
    rw [hh]
    by_cases hc : c ∈ d.val
    · simp [extendTableau, hc]
    · simp [extendTableau, hc]
  · constructor
    · intro h
      exact (hp (Finset.mem_filter.mp h).1).elim
    · intro h
      exact (hp (d.property.1 h)).elim

@[simp] theorem extendTableau_restrictTableau {n r : ℕ} {p : Partition n}
    (T : SemistandardFilling p (r + 1)) :
    extendTableau (trimmedSubshape T) (restrictTableau T) = T := by
  apply Subtype.ext
  funext c
  apply Fin.ext
  by_cases hc : c.val ∈ (trimmedSubshape T).val
  · simp only [extendTableau, dite_eq_left hc, Fin.val_castSucc]
    rfl
  · have hh := (mem_trimmedSubshape T c).not.mp hc
    have hb := (T.val c).isLt
    simp only [extendTableau, dite_eq_right hc, Fin.val_last]
    omega

/-- Extension by the largest letter parametrizes all tableaux, uniquely. -/
def tableauBranchEquiv {n : ℕ} (p : Partition n) (r : ℕ) :
    (Σ d : HorizontalSubshape p, SemistandardFilling (subshapePartition d) r) ≃
      SemistandardFilling p (r + 1) :=
  Equiv.ofBijective (fun a => extendTableau a.1 a.2) (by
    constructor
    · rintro ⟨d, T⟩ ⟨e, U⟩ h
      change extendTableau d T = extendTableau e U at h
      have hd : d = e := by
        rw [← trimmedSubshape_extendTableau d T, h, trimmedSubshape_extendTableau]
      subst e
      have hTU : T = U := by
        apply Subtype.ext
        funext c
        apply Fin.ext
        have hc : c.val ∈ d.val := by
          have hc : c.val ∈ diagram (subshapePartition d) := c.property
          rwa [diagram_subshapePartition] at hc
        have hv := congrArg (fun V : SemistandardFilling p (r + 1) =>
          (V.val (subshapeCell d c)).val) h
        simpa only [extendTableau, subshapeCell, dite_eq_left hc, Fin.val_castSucc] using hv
      subst U
      rfl
    · intro T
      exact ⟨⟨trimmedSubshape T, restrictTableau T⟩, extendTableau_restrictTableau T⟩)

theorem fillingWeight_extendTableau {n r : ℕ} {p : Partition n}
    (d : HorizontalSubshape p) (T : SemistandardFilling (subshapePartition d) r)
    (f : Filling p (r + 1))
    (hf : ∀ c, f c = if hc : c.val ∈ d.val then
      (T.val ⟨c.val, by change c.val ∈ diagram (subshapePartition d); rwa [diagram_subshapePartition]⟩).castSucc
      else Fin.last r) :
    fillingWeight f =
      MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r+1)) (tableauWeight T) *
        (MvPolynomial.X (Fin.last r) : Alphabet (r+1)) ^ (n-d.val.card) := by
  classical
  let P : Cell p → Prop := fun c => c.val ∈ d.val
  let e : Cell (subshapePartition d) ≃ {c : Cell p // P c} :=
    { toFun := fun c => ⟨⟨c.val, d.property.1 (by
          have hc := c.property
          change c.val ∈ diagram (subshapePartition d) at hc
          rwa [diagram_subshapePartition] at hc)⟩, by
          have hc := c.property
          change c.val ∈ diagram (subshapePartition d) at hc
          rwa [diagram_subshapePartition] at hc⟩
      invFun := fun c => ⟨c.val.val, by
        change c.val.val ∈ diagram (subshapePartition d)
        rw [diagram_subshapePartition]
        exact c.property⟩
      left_inv := fun c => rfl
      right_inv := fun c => rfl }
  have he : Fintype.card {c : Cell p // P c} = d.val.card := by
    rw [← Fintype.card_congr e]
    change Fintype.card ↥(cells (subshapePartition d)) = _
    rw [Fintype.card_coe]
    change (diagram (subshapePartition d)).card = _
    rw [diagram_subshapePartition]
  have hc : Fintype.card {c : Cell p // ¬P c} = n-d.val.card := by
    rw [Fintype.card_subtype_compl, he]
    congr 1
    change Fintype.card ↥(cells p) = n
    rw [Fintype.card_coe]
    exact diagram_card p
  change (∏ c : Cell p, MvPolynomial.X (f c)) = _
  rw [← Fintype.prod_subtype_mul_prod_subtype P]
  have hinside : (∏ c : {c : Cell p // P c}, MvPolynomial.X (f c.val)) =
      MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r+1)) (tableauWeight T) := by
    change _ = MvPolynomial.rename Fin.castSucc
      (∏ c : Cell (subshapePartition d), MvPolynomial.X (T.val c))
    rw [map_prod]
    symm
    apply Fintype.prod_equiv e
    intro c
    rw [MvPolynomial.rename_X, hf]
    dsimp [e]
    have hmem : c.val ∈ d.val := by
      have hh := c.property
      change c.val ∈ diagram (subshapePartition d) at hh
      rwa [diagram_subshapePartition] at hh
    simp only [ite_eq_left hmem]
  rw [hinside]
  congr 1
  calc
    _ = ∏ _c : {c : Cell p // ¬P c},
        (MvPolynomial.X (Fin.last r) : Alphabet (r+1)) := by
      apply Finset.prod_congr rfl
      intro c _
      rw [hf, dite_eq_right c.property]
    _ = _ := by simp [hc]

theorem tableauSum_eq_sum_tableauWeight {n : ℕ} (p : Partition n) (r : ℕ) :
    tableauSum p r = ∑ T : SemistandardFilling p r, tableauWeight T := by
  classical
  simp only [tableauSum, Specs.AdvancedFiniteGroupRepresentations.tableauSum,
    Specs.AdvancedFiniteGroupRepresentations.semistandardFillings,
    tableauWeight, Specs.AdvancedFiniteGroupRepresentations.tableauWeight]
  exact Finset.sum_subtype _ (by simp) _

/-- The literal semistandard-tableau sum branches by the largest-letter strip. -/
theorem tableauSum_succ_alphabet {n : ℕ} (p : Partition n) (r : ℕ) :
    tableauSum p (r + 1) =
      ∑ d : HorizontalSubshape p,
        MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r + 1))
          (tableauSum (subshapePartition d) r) *
          (MvPolynomial.X (Fin.last r) : Alphabet (r + 1)) ^ (n - d.val.card) := by
  classical
  calc
    tableauSum p (r + 1) = ∑ T : SemistandardFilling p (r+1), tableauWeight T :=
      tableauSum_eq_sum_tableauWeight p (r+1)
    _ = ∑ a : Σ d : HorizontalSubshape p, SemistandardFilling (subshapePartition d) r,
        tableauWeight (extendTableau a.1 a.2) :=
      (Fintype.sum_equiv (tableauBranchEquiv p r) _ _ (fun a => rfl)).symm
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro d _
      have hw (T : SemistandardFilling (subshapePartition d) r) :
          tableauWeight (extendTableau d T) =
          MvPolynomial.rename (Fin.castSucc : Fin r → Fin (r+1)) (tableauWeight T) *
            (MvPolynomial.X (Fin.last r) : Alphabet (r+1)) ^ (n-d.val.card) :=
        fillingWeight_extendTableau d T _ (fun _ => rfl)
      simp_rw [hw]
      rw [← Finset.sum_mul, ← map_sum, ← tableauSum_eq_sum_tableauWeight]

/-- Alphabet induction identifies the padded determinant with the literal tableau sum. -/
theorem paddedJacobiTrudi_eq_tableauSum {n : ℕ} (p : Partition n) (r m : ℕ)
    (hm : length p ≤ m) :
    paddedJacobiTrudi p r m = tableauSum p r := by
  induction r generalizing n m with
  | zero => rw [paddedJacobiTrudi_no_variables p m hm, tableauSum_no_variables]
  | succ r ih =>
    calc
      paddedJacobiTrudi p (r + 1) m = paddedJacobiTrudi p (r + 1) (m + 1) :=
        (paddedJacobiTrudi_succ p (r + 1) m hm).symm
      _ = _ := paddedJacobiTrudi_succ_alphabet p r (by omega)
      _ = tableauSum p (r + 1) := by
        rw [tableauSum_succ_alphabet p r]
        apply Finset.sum_congr rfl
        intro d _
        rw [ih (subshapePartition d) (m + 1) ((subshape_length_le d).trans (by omega))]

/-- The canonical alternant quotient has the semistandard-tableau expansion. -/
theorem schurPolynomial_eq_tableauSum {n : ℕ} (p : Partition n) (r : ℕ) :
    schurPolynomial p r = tableauSum p r := by
  rw [← paddedJacobiTrudi_eq_schurPolynomial p r (length p) le_rfl]
  exact paddedJacobiTrudi_eq_tableauSum p r (length p) le_rfl

/-- The three formulas of FR-C04, including the zero-variable empty shape. -/
theorem schur_three_formulas {n : ℕ} (p : Partition n) (r : ℕ) (hr : length p ≤ r) :
    vandermonde r * schurPolynomial p r = partitionAlternant r p ∧
    schurPolynomial p r = jacobiTrudi p r ∧
    schurPolynomial p r = tableauSum p r :=
  ⟨schurPolynomial_characterization p r hr, schurPolynomial_eq_jacobiTrudi p r hr,
    schurPolynomial_eq_tableauSum p r⟩

end AdvancedFiniteGroupRepresentations
