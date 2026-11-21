import MathGenome.Internal.Specs.D05.M15.DeterminantLine.Laplace
import MathGenome.Internal.D05.M05.DetDefinition
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D05.M15.DeterminantLine.Laplace
open scoped BigOperators
open Specs.D05.M15.DeterminantLine.Laplace

/-- Keep precisely the two rectangles I×J and Iᶜ×Jᶜ. -/
def pairedMask {R : Type*} [Zero R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (I J : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => if (i ∈ I ↔ j ∈ J) then A i j else 0

/-- Splitting every column into its I and Iᶜ parts expands the determinant
into paired masks, with no sign or cardinality assumptions. -/
theorem det_eq_sum_pairedMask {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (I : Finset (Fin n)) :
    A.det = ∑ J : Finset (Fin n), (pairedMask A I J).det := by
  classical
  let B : Matrix (Fin n) (Fin n) R := fun j i => if i ∈ I then A i j else 0
  let C : Matrix (Fin n) (Fin n) R := fun j i => if i ∈ I then 0 else A i j
  have hBC : B + C = A.transpose := by
    ext j i
    simp only [Matrix.add_apply, B, C, Matrix.transpose_apply]
    split_ifs <;> simp
  rw [← Matrix.det_transpose A, ← hBC]
  change Matrix.detRowAlternating (B + C) = _
  rw [Matrix.detRowAlternating.map_add_univ]
  apply Finset.sum_congr rfl
  intro J _
  rw [← Matrix.det_transpose (pairedMask A I J)]
  congr 1
  ext j i
  simp only [Finset.piecewise, pairedMask, Matrix.transpose_apply, B, C]
  by_cases hi : i ∈ I <;> by_cases hj : j ∈ J <;> simp [hi, hj]

/-- A mask with unequal block sizes has zero determinant. The Leibniz
terms would otherwise induce a bijection from J to I. -/
theorem det_pairedMask_eq_zero {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (I J : Finset (Fin n))
    (hcard : I.card ≠ J.card) : (pairedMask A I J).det = 0 := by
  classical
  rw [Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ _
  suffices hp : (∏ j, pairedMask A I J (σ j) j) = 0 by rw [hp, smul_zero]
  by_contra hp
  have hm : ∀ j, σ j ∈ I ↔ j ∈ J := by
    intro j
    by_contra h
    exact hp (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [pairedMask, h]))
  have hIJ : I = J.image σ := by
    ext i
    constructor
    · intro hi
      exact Finset.mem_image.mpr ⟨σ.symm i, (hm _).mp (by simpa using hi),
        σ.apply_symm_apply i⟩
    · rintro hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact (hm j).mpr hj
  apply hcard
  rw [hIJ, Finset.card_image_of_injective J σ.injective]

/-- Only column sets of the specified cardinality contribute. -/
theorem det_eq_sum_pairedMask_card {R : Type*} [CommRing R] {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (I : Set.powersetCard (Fin n) k) :
    A.det = ∑ J : Set.powersetCard (Fin n) k, (pairedMask A I.val J.val).det := by
  classical
  rw [det_eq_sum_pairedMask A I.val]
  have hz : (∑ J : {J : Finset (Fin n) // ¬J.card = k},
      (pairedMask A I.val J.val).det) = 0 := by
    apply Finset.sum_eq_zero
    intro J _
    exact det_pairedMask_eq_zero A I.val J.val
      (by simpa [I.prop, ne_comm] using J.prop)
  have h := Fintype.sum_subtype_add_sum_subtype
    (fun J : Finset (Fin n) => J.card = k)
    (fun J => (pairedMask A I.val J).det)
  rw [hz, add_zero] at h
  calc
    _ = ∑ J : {J : Finset (Fin n) // J.card = k}, (pairedMask A I.val J.val).det := h.symm
    _ = _ := by
      let e : {J : Finset (Fin n) // J.card = k} ≃ Set.powersetCard (Fin n) k :=
        ⟨fun J => ⟨J.val, J.prop⟩, fun J => ⟨J.val, J.prop⟩,
          fun _ => rfl, fun _ => rfl⟩
      exact Fintype.sum_equiv e (fun J => (pairedMask A I.val J.val).det)
        (fun J => (pairedMask A I.val J.val).det) (fun _ => rfl)

/-- In an increasing two-block permutation all inversions are cross-block. -/
theorem sign_two_increasing_blocks {k m : ℕ} (σ : Equiv.Perm (Fin (k+m)))
    (hl : StrictMono (fun i : Fin k => σ (i.castAdd m)))
    (hr : StrictMono (fun j : Fin m => σ (j.natAdd k))) :
    (Equiv.Perm.sign σ : ℤ) =
      ∏ i : Fin k, ∏ j : Fin m,
        if σ (j.natAdd k) < σ (i.castAdd m) then (-1 : ℤ) else 1 := by
  have hsg := congrArg (fun u : ℤˣ => (u : ℤ)) σ.sign_eq_prod_prod_Ioi
  simp only [Units.coe_prod, apply_ite, Units.val_one, Units.val_neg] at hsg
  have hinner (i : Fin (k+m)) :
      (∏ j ∈ Finset.Ioi i, if σ i < σ j then (1 : ℤ) else -1) =
      ∏ j, if i < j ∧ σ j < σ i then (-1 : ℤ) else 1 := by
    rw [show Finset.Ioi i = Finset.univ.filter (fun j => i < j) by ext; simp,
      Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro j _
    by_cases hij : i < j
    · have hne : σ i ≠ σ j := σ.injective.ne hij.ne
      rcases lt_or_gt_of_ne hne with h | h <;> simp [hij, h, not_lt_of_gt h]
    · simp [hij]
  rw [hsg]
  simp_rw [hinner]
  rw [Fin.prod_univ_add]
  have hleft (i : Fin k) :
      (∏ j : Fin (k+m), if i.castAdd m < j ∧ σ j < σ (i.castAdd m)
        then (-1 : ℤ) else 1) =
      ∏ j : Fin m, if σ (j.natAdd k) < σ (i.castAdd m) then (-1 : ℤ) else 1 := by
    rw [Fin.prod_univ_add]
    have hone : (∏ j : Fin k, if i.castAdd m < j.castAdd m ∧
        σ (j.castAdd m) < σ (i.castAdd m) then (-1 : ℤ) else 1) = 1 := by
      apply Finset.prod_eq_one
      intro j _
      have hiff : i.castAdd m < j.castAdd m ↔ i < j := Iff.rfl
      have hnot : ¬(i < j ∧ σ (j.castAdd m) < σ (i.castAdd m)) := by
        rintro ⟨hij, hji⟩
        exact (hl hij).not_gt hji
      simp only [hiff, hnot, ↓reduceIte]
    rw [hone, one_mul]
    apply Finset.prod_congr rfl
    intro j _
    have hij : i.castAdd m < j.natAdd k := by
      simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
      omega
    simp [hij]
  have hright (i : Fin m) :
      (∏ j : Fin (k+m), if i.natAdd k < j ∧ σ j < σ (i.natAdd k)
        then (-1 : ℤ) else 1) = 1 := by
    rw [Fin.prod_univ_add]
    have hone : (∏ j : Fin k, if i.natAdd k < j.castAdd m ∧
        σ (j.castAdd m) < σ (i.natAdd k) then (-1 : ℤ) else 1) = 1 := by
      apply Finset.prod_eq_one
      intro j _
      have hij : ¬i.natAdd k < j.castAdd m := by
        simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
        omega
      simp [hij]
    rw [hone, one_mul]
    apply Finset.prod_eq_one
    intro j _
    have hiff : i.natAdd k < j.natAdd k ↔ i < j := Fin.natAdd_lt_natAdd_iff k
    have hnot : ¬(i < j ∧ σ (j.natAdd k) < σ (i.natAdd k)) := by
      rintro ⟨hij, hji⟩
      exact (hr hij).not_gt hji
    simp only [hiff, hnot, ↓reduceIte]
  simp_rw [hleft, hright]
  simp

/-- Counting positions strictly below an element of Fin. -/
theorem sum_positions_lt {q : ℕ} (a : Fin q) :
    (∑ j : Fin q, if j < a then (1 : ℕ) else 0) = a.val := by
  rw [Finset.sum_boole]
  have hset : Finset.univ.filter (fun j : Fin q => j < a) = Finset.Iio a := by
    ext; simp
  simp only [hset, Fin.card_Iio, Nat.cast_id]

/-- The sign of an increasing two-block permutation is determined by the
positions in its first block; the second factor depends only on k. -/
theorem sign_two_blocks_positions {k m : ℕ} (σ : Equiv.Perm (Fin (k+m)))
    (hl : StrictMono (fun i : Fin k => σ (i.castAdd m)))
    (hr : StrictMono (fun j : Fin m => σ (j.natAdd k))) :
    (Equiv.Perm.sign σ : ℤ) =
      (-1 : ℤ) ^ ((∑ i : Fin k, (σ (i.castAdd m)).val) + ∑ i : Fin k, i.val) := by
  rw [sign_two_increasing_blocks σ hl hr]
  have hterm (i : Fin k) :
      (∏ j : Fin m, if σ (j.natAdd k) < σ (i.castAdd m) then (-1 : ℤ) else 1) =
      (-1 : ℤ) ^ ((σ (i.castAdd m)).val + i.val) := by
    let c : ℕ := ∑ j : Fin m, if σ (j.natAdd k) < σ (i.castAdd m) then 1 else 0
    have hc : i.val + c = (σ (i.castAdd m)).val := by
      have h := Equiv.sum_comp σ (fun j => if j < σ (i.castAdd m) then (1 : ℕ) else 0)
      rw [Fin.sum_univ_add, sum_positions_lt] at h
      simp_rw [hl.lt_iff_lt] at h
      rw [sum_positions_lt] at h
      exact h
    have hp : (∏ j : Fin m,
        if σ (j.natAdd k) < σ (i.castAdd m) then (-1 : ℤ) else 1) = (-1 : ℤ) ^ c := by
      dsimp [c]
      rw [← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_congr rfl
      intro j _
      split_ifs <;> simp
    rw [hp, ← hc, show i.val + c + i.val = c + 2*i.val by omega, pow_add, pow_mul]
    simp
  simp_rw [hterm]
  rw [Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib]

/-- The increasing row shuffle, placing I first and Iᶜ second. -/
def subsetShuffle {n k : ℕ} (I : Set.powersetCard (Fin n) k) :
    Fin k ⊕ Fin (n-k) ≃ Fin n :=
  ((I.val.orderIsoOfFin I.prop).toEquiv.sumCongr
    (((complement I).val.orderIsoOfFin (complement I).prop).toEquiv.trans
      (Equiv.subtypeEquivRight (fun _ => Finset.mem_compl)))).trans
        (Equiv.sumCompl (fun i => i ∈ I.val))

@[simp] theorem subsetShuffle_inl {n k : ℕ} (I : Set.powersetCard (Fin n) k)
    (i : Fin k) : subsetShuffle I (Sum.inl i) = I.val.orderEmbOfFin I.prop i := rfl

@[simp] theorem subsetShuffle_inr {n k : ℕ} (I : Set.powersetCard (Fin n) k)
    (i : Fin (n-k)) : subsetShuffle I (Sum.inr i) =
      (complement I).val.orderEmbOfFin (complement I).prop i := rfl

@[simp] theorem complement_enum_not_mem {n k : ℕ}
    (I : Set.powersetCard (Fin n) k) (i : Fin (n-k)) :
    (complement I).val.orderEmbOfFin (complement I).prop i ∉ I.val :=
  Finset.mem_compl.mp (Finset.orderEmbOfFin_mem (complement I).val (complement I).prop i)

/-- The same shuffle, expressed as a permutation on its concatenated positions. -/
def blockPermutation {n k : ℕ} (I : Set.powersetCard (Fin n) k) :
    Equiv.Perm (Fin (k + (n-k))) :=
  finSumFinEquiv.symm |>.trans (subsetShuffle I) |>.trans
    (finCongr (Nat.add_sub_of_le (by
      simpa using (Finset.card_le_univ I.val))).symm)

@[simp] theorem blockPermutation_left_val {n k : ℕ}
    (I : Set.powersetCard (Fin n) k) (i : Fin k) :
    (blockPermutation I (i.castAdd (n-k))).val = (I.val.orderEmbOfFin I.prop i).val := by
  simp [blockPermutation]

@[simp] theorem blockPermutation_right_val {n k : ℕ}
    (I : Set.powersetCard (Fin n) k) (i : Fin (n-k)) :
    (blockPermutation I (i.natAdd k)).val =
      ((complement I).val.orderEmbOfFin (complement I).prop i).val := by
  simp [blockPermutation]

theorem blockPermutation_sign {n k : ℕ} (I : Set.powersetCard (Fin n) k) :
    (Equiv.Perm.sign (blockPermutation I) : ℤ) =
      (-1 : ℤ) ^ ((∑ i ∈ I.val, i.val) + ∑ i : Fin k, i.val) := by
  have hl : StrictMono (fun i : Fin k => blockPermutation I (i.castAdd (n-k))) := by
    intro i j hij
    simpa only [Fin.lt_def, blockPermutation_left_val] using
      (I.val.orderEmbOfFin I.prop).strictMono hij
  have hr : StrictMono (fun j : Fin (n-k) => blockPermutation I (j.natAdd k)) := by
    intro i j hij
    simpa only [Fin.lt_def, blockPermutation_right_val] using
      ((complement I).val.orderEmbOfFin (complement I).prop).strictMono hij
  rw [sign_two_blocks_positions (blockPermutation I) hl hr]
  simp only [blockPermutation_left_val]
  congr 2
  simpa only [Finset.map_orderEmbOfFin_univ, RelEmbedding.coe_toEmbedding] using
    (Finset.sum_map Finset.univ (I.val.orderEmbOfFin I.prop).toEmbedding
      (fun i : Fin n => i.val)).symm

/-- The two triangular-number contributions cancel. The additional two
copies of k from one-based positions also have even parity. -/
theorem shuffle_pair_sign {n k : ℕ} (I J : Set.powersetCard (Fin n) k) :
    (Equiv.Perm.sign ((subsetShuffle J).symm.trans (subsetShuffle I)) : ℤ) =
      (-1 : ℤ) ^ (indexSum I.val + indexSum J.val) := by
  let e : Fin (k+(n-k)) ≃ Fin n := finCongr (Nat.add_sub_of_le (by
    simpa using (Finset.card_le_univ I.val)))
  have hp : Equiv.permCongr e (blockPermutation I * (blockPermutation J)⁻¹) =
      (subsetShuffle J).symm.trans (subsetShuffle I) := by
    ext x
    simp [e, blockPermutation, Equiv.permCongr_apply]
  rw [← hp, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv,
    Units.val_mul, blockPermutation_sign, blockPermutation_sign, ← pow_add]
  have hi : indexSum I.val = (∑ i ∈ I.val, i.val) + k := by
    simp [indexSum, Finset.sum_add_distrib]
  have hj : indexSum J.val = (∑ j ∈ J.val, j.val) + k := by
    simp [indexSum, Finset.sum_add_distrib]
  rw [hi, hj,
    show ((∑ i ∈ I.val, i.val) + ∑ i : Fin k, i.val) +
        ((∑ j ∈ J.val, j.val) + ∑ i : Fin k, i.val) =
        ((∑ i ∈ I.val, i.val) + (∑ j ∈ J.val, j.val)) + 2*(∑ i : Fin k, i.val) by omega,
    show ((∑ i ∈ I.val, i.val) + k) + ((∑ j ∈ J.val, j.val) + k) =
        ((∑ i ∈ I.val, i.val) + (∑ j ∈ J.val, j.val)) + 2*k by omega]
  simp [pow_add, pow_mul]

/-- After the two increasing shuffles a paired mask is block diagonal. -/
theorem pairedMask_submatrix_shuffle {R : Type*} [Zero R] {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (I J : Set.powersetCard (Fin n) k) :
    (pairedMask A I.val J.val).submatrix (subsetShuffle I) (subsetShuffle J) =
      Matrix.fromBlocks
        (A.submatrix (I.val.orderEmbOfFin I.prop) (J.val.orderEmbOfFin J.prop))
        0 0
        (A.submatrix ((complement I).val.orderEmbOfFin (complement I).prop)
          ((complement J).val.orderEmbOfFin (complement J).prop)) := by
  ext (i | i) (j | j) <;>
    simp [pairedMask, Finset.orderEmbOfFin_mem]

/-- The determinant of each mask factors as the two increasing minors,
with the sign of the explicitly constructed row/column shuffle. -/
theorem det_pairedMask_factor {K : Type*} [Field K] {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (I J : Set.powersetCard (Fin n) k) :
    (pairedMask A I.val J.val).det =
      (Equiv.Perm.sign ((subsetShuffle J).symm.trans (subsetShuffle I)) : ℤ) *
        orderedMinor A I J * orderedMinor A (complement I) (complement J) := by
  have h := Matrix.det_reindex (subsetShuffle I).symm (subsetShuffle J).symm
    (pairedMask A I.val J.val)
  change ((pairedMask A I.val J.val).submatrix (subsetShuffle I) (subsetShuffle J)).det = _ at h
  rw [pairedMask_submatrix_shuffle, Matrix.det_fromBlocks_zero₂₁] at h
  unfold orderedMinor
  rw [D05.M05.DetDefinition.matrix_det_bridge, D05.M05.DetDefinition.matrix_det_bridge]
  let s : ℤˣ := Equiv.Perm.sign ((subsetShuffle J).symm.trans (subsetShuffle I))
  simp only [Equiv.symm_symm] at h
  change _ = ((s : ℤ) : K) * _ at h
  have hs : ((s : ℤ) : K) * ((s : ℤ) : K) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  calc
    _ = 1 * (pairedMask A I.val J.val).det := (one_mul _).symm
    _ = ((s : ℤ) : K) * (((s : ℤ) : K) * (pairedMask A I.val J.val).det) := by rw [← mul_assoc, hs]
    _ = _ := by rw [← h]; ring

/-- General Laplace expansion with increasing complementary minors and the
paper's one-based sign, valid also in characteristic two and in degree zero. -/
theorem general_laplace : Specs.D05.M15.DeterminantLine.Laplace.general_laplace := by
  intro K _ n A k I
  rw [D05.M05.DetDefinition.matrix_det_bridge, det_eq_sum_pairedMask_card A I]
  apply Finset.sum_congr rfl
  intro J _
  rw [det_pairedMask_factor]
  have hs := congrArg (fun z : ℤ => (z : K)) (shuffle_pair_sign I J)
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one] at hs
  rw [hs]

/-- Adding the two one-based offsets to a cofactor exponent changes it by 2. -/
theorem cofactor_sign {R : Type*} [Ring R] (i j : ℕ) :
    (-1 : R) ^ ((i+1)+(j+1)) = (-1 : R) ^ (i+j) := by
  rw [show (i+1)+(j+1) = (i+j)+2 by omega, pow_add]
  simp

theorem cofactor_expansion :
    Specs.D05.M15.DeterminantLine.Laplace.cofactor_expansion := by
  intro K _ n A i
  rw [D05.M05.DetDefinition.matrix_det_bridge, Matrix.det_succ_row]
  apply Finset.sum_congr rfl
  intro j _
  rw [D05.M05.DetDefinition.matrix_det_bridge, cofactor_sign]

end D05.M15.DeterminantLine.Laplace
