import MathGenome.Internal.Specs.D05.M09.RealComplexBridge.Orientation
import MathGenome.Internal.D05.M09.RealComplexBridge.Realification
import MathGenome.Internal.D05.M05.Orientation
import MathGenome.Internal.D05.Foundations.PermutationSign
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum

noncomputable section
open scoped BigOperators
namespace D05.M09.RealComplexBridge.Orientation
open Specs.D05.M09.RealComplexBridge.Orientation

abbrev groupingPermutation := Specs.D05.M09.RealComplexBridge.Orientation.groupingPermutation
abbrev groupedBasis := @Specs.D05.M09.RealComplexBridge.Orientation.groupedBasis
abbrev interleavedBasis := @Specs.D05.M09.RealComplexBridge.Orientation.interleavedBasis
abbrev canonicalOrientation := Specs.D05.M09.RealComplexBridge.Orientation.canonicalOrientation
abbrev complexOrientation := @Specs.D05.M09.RealComplexBridge.Orientation.complexOrientation
abbrev greubOrientation := @Specs.D05.M09.RealComplexBridge.Orientation.greubOrientation

private theorem groupedIndex_zero (n : ℕ) (j : Fin n) :
    groupedIndex n (0,j) = Fin.castAdd n j := by
  apply Fin.ext
  simp [groupedIndex, finProdFinEquiv]

private theorem groupedIndex_one (n : ℕ) (j : Fin n) :
    groupedIndex n (1,j) = Fin.natAdd n j := by
  apply Fin.ext
  simp [groupedIndex, finProdFinEquiv, Nat.add_comm]
theorem index_positions : Specs.D05.M09.RealComplexBridge.Orientation.index_positions := by
  intro n j
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [interleavedIndex, finProdFinEquiv]
  · simp [interleavedIndex, finProdFinEquiv, Nat.add_comm]
  · rw [← groupedIndex_zero]
    exact (groupedIndex n).symm_apply_apply (0,j) |> congrArg (interleavedIndex n)
  · rw [← groupedIndex_one]
    exact (groupedIndex n).symm_apply_apply (1,j) |> congrArg (interleavedIndex n)

private theorem interleaved_apply {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (i : Fin 2) (j : Fin n) :
    interleavedBasis b (interleavedIndex n (i,j)) =
      (Complex.basisOneI i) • b j := by
  simp [interleavedBasis,
    Specs.D05.M09.RealComplexBridge.Orientation.interleavedBasis,
    Specs.D05.M09.RealComplexBridge.Orientation.groupedBasis,
    Specs.D05.M09.RealComplexBridge.Orientation.groupingPermutation,
    Module.Basis.smulTower_apply]
theorem basis_vectors : Specs.D05.M09.RealComplexBridge.Orientation.basis_vectors := by
  intro V _ _ n b j
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← groupedIndex_zero]
    simp [Specs.D05.M09.RealComplexBridge.Orientation.groupedBasis,
      Module.Basis.smulTower_apply, Complex.coe_basisOneI]
  · rw [← groupedIndex_one]
    simp [Specs.D05.M09.RealComplexBridge.Orientation.groupedBasis,
      Module.Basis.smulTower_apply, Complex.coe_basisOneI]
  · simpa [Complex.coe_basisOneI] using interleaved_apply b 0 j
  · simpa [Complex.coe_basisOneI] using interleaved_apply b 1 j

private theorem reindex_det {V : Type*} [AddCommGroup V] [Module ℝ V] {m : ℕ}
    (b c : Module.Basis (Fin m) ℝ V) (σ : Equiv.Perm (Fin m)) :
    (b.reindex σ).det (c.reindex σ) = b.det c := by
  rw [Module.Basis.det_reindex]
  have h : ((c.reindex σ : Fin m → V) ∘ σ) = c := by
    ext i
    simp
  rw [h]
theorem reindex_transition : Specs.D05.M09.RealComplexBridge.Orientation.reindex_transition := by
  intro V _ _ m b c σ
  rw [D05.M05.Orientation.conversion_det_basis, D05.M05.Orientation.conversion_det_basis]
  exact reindex_det b c σ

private theorem grouped_map {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (b c : Module.Basis (Fin n) ℂ V) :
    (groupedBasis b).map ((b.equiv c (Equiv.refl _)).restrictScalars ℝ) = groupedBasis c := by
  ext i
  obtain ⟨⟨k,j⟩, rfl⟩ := (groupedIndex n).surjective i
  simp [Specs.D05.M09.RealComplexBridge.Orientation.groupedBasis,
    Module.Basis.smulTower_apply, Module.Basis.equiv_apply]
theorem transition_determinants :
    Specs.D05.M09.RealComplexBridge.Orientation.transition_determinants := by
  intro V _ _ n b c
  let := Module.Finite.of_basis b
  let T := b.equiv c (Equiv.refl _)
  have hT : LinearMap.det T.toLinearMap = b.det c := by
    have h := b.det_comp T.toLinearMap b
    simpa only [T, Module.Basis.equiv_apply, Equiv.refl_apply, b.det_self, mul_one, Function.comp_def, LinearEquiv.coe_coe] using h.symm
  have hg : _root_.D05.M05.determinant
      (Specs.D05.M04.ChangeBasis.changeMatrix_value (groupedBasis b) (groupedBasis c)) =
        ‖b.det c‖^2 := by
    rw [← grouped_map b c, D05.M05.Orientation.conversion_map_det]
    change LinearMap.det (T.toLinearMap.restrictScalars ℝ) = _
    rw [Realification.determinant]
    rw [hT]
  refine ⟨hg, ?_⟩
  change _root_.D05.M05.determinant (Specs.D05.M04.ChangeBasis.changeMatrix_value
    ((groupedBasis b).reindex (groupingPermutation n))
    ((groupedBasis c).reindex (groupingPermutation n))) = _
  rw [reindex_transition, hg]
theorem transition_positive : Specs.D05.M09.RealComplexBridge.Orientation.transition_positive := by
  intro V _ _ n b c
  have hp : 0 < ‖b.det c‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (b.isUnit_det c).ne_zero)
  constructor
  · change 0 < _root_.D05.M05.determinant _
    rw [(transition_determinants b c).2]
    exact hp
  · change 0 < _root_.D05.M05.determinant _
    rw [(transition_determinants b c).1]
    exact hp
theorem basis_independence : Specs.D05.M09.RealComplexBridge.Orientation.basis_independence := by
  intro V _ _ n b c
  exact ⟨(D05.M05.Orientation.class_eq_iff _ _).mpr (transition_positive b c).1,
    (D05.M05.Orientation.class_eq_iff _ _).mpr (transition_positive b c).2⟩

theorem canonical_orientation_basis :
    Specs.D05.M09.RealComplexBridge.Orientation.canonical_orientation_basis := by
  intro V _ _ _ b
  exact (basis_independence (Module.finBasis ℂ V) b).1
theorem reindex_conjugation : Specs.D05.M09.RealComplexBridge.Orientation.reindex_conjugation := by
  intro V _ _ m b c σ
  dsimp only
  simp only [Matrix.transpose_submatrix, Matrix.transpose_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.submatrix_mul_equiv _ _ _ σ.symm _, Matrix.one_mul]
    rfl
  · simpa using (Matrix.submatrix_mul_equiv (1 : Matrix (Fin m) (Fin m) ℝ) 1
      σ.symm (Equiv.refl _) σ.symm)
  · have hl := Matrix.one_submatrix_mul σ.symm (Equiv.refl (Fin m))
      (Specs.D05.M04.ChangeBasis.changeMatrix_value b c)
    simp only [Equiv.refl_symm, Equiv.coe_refl, Function.id_comp] at hl
    rw [hl]
    have hr := Matrix.mul_submatrix_one (Equiv.refl (Fin m)) σ.symm
      ((Specs.D05.M04.ChangeBasis.changeMatrix_value b c).submatrix σ.symm id)
    simp only [Equiv.coe_refl, Equiv.refl_symm, Function.id_comp] at hr
    rw [hr]
    ext i j
    simp [Specs.D05.M04.ChangeBasis.changeMatrix_value,
      Specs.D05.M04.MatrixOfMap.matrixOfMap_value, LinearMap.toMatrix_apply,
      Module.Basis.toMatrix_apply]
theorem interleaved_invariants : Specs.D05.M09.RealComplexBridge.Orientation.interleaved_invariants := by
  intro V _ _ n b T
  let := Module.Finite.of_basis b
  constructor
  · rw [LinearMap.det_toMatrix, Realification.determinant]
  · rw [LinearMap.charpoly_toMatrix, Realification.operator_charpoly]

private theorem shuffle_left_val (n : ℕ) (j : Fin n) :
    (groupingPermutation n (Fin.castAdd n j)).val = 2*j.val := by
  rw [(index_positions n j).2.2.1]
  exact (index_positions n j).1

private theorem shuffle_right_val (n : ℕ) (j : Fin n) :
    (groupingPermutation n (Fin.natAdd n j)).val = 2*j.val+1 := by
  rw [(index_positions n j).2.2.2]
  exact (index_positions n j).2.1
theorem grouping_inversions : Specs.D05.M09.RealComplexBridge.Orientation.grouping_inversions := by
  intro n
  have hc : D05.Foundations.inversionCount (groupingPermutation n) =
      ∑ i : Fin (n+n), ∑ j : Fin (n+n),
        if i < j ∧ groupingPermutation n j < groupingPermutation n i then 1 else 0 := by
    unfold D05.Foundations.inversionCount
    apply Finset.sum_congr rfl
    intro i _
    rw [show (Finset.Ioi i).filter (fun j => groupingPermutation n j < groupingPermutation n i) =
      Finset.univ.filter (fun j => i < j ∧ groupingPermutation n j < groupingPermutation n i) by
        ext j; simp]
    exact Finset.card_filter _ _
  have hll (i j : Fin n) : ¬(Fin.castAdd n i < Fin.castAdd n j ∧
      groupingPermutation n (Fin.castAdd n j) < groupingPermutation n (Fin.castAdd n i)) := by
    simp only [Fin.lt_def, Fin.val_castAdd, shuffle_left_val]
    omega
  have hlr (i j : Fin n) : (Fin.castAdd n i < Fin.natAdd n j ∧
      groupingPermutation n (Fin.natAdd n j) < groupingPermutation n (Fin.castAdd n i)) ↔ j < i := by
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd, shuffle_left_val, shuffle_right_val]
    omega
  have hrl (i j : Fin n) : ¬(Fin.natAdd n i < Fin.castAdd n j ∧
      groupingPermutation n (Fin.castAdd n j) < groupingPermutation n (Fin.natAdd n i)) := by
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd, shuffle_left_val, shuffle_right_val]
    omega
  have hrr (i j : Fin n) : ¬(Fin.natAdd n i < Fin.natAdd n j ∧
      groupingPermutation n (Fin.natAdd n j) < groupingPermutation n (Fin.natAdd n i)) := by
    simp only [Fin.lt_def, Fin.val_natAdd, shuffle_right_val]
    omega
  rw [hc]
  simp only [Fin.sum_univ_add, hll, hlr, hrl, hrr, ite_false, Finset.sum_const_zero,
    zero_add, add_zero]
  have hf (i : Fin n) : (∑ j : Fin n, if j < i then 1 else 0) = i.val := by
    rw [← Finset.card_filter]
    rw [show Finset.univ.filter (fun j : Fin n => j < i) = Finset.Iio i by ext j; simp]
    exact Fin.card_Iio i
  simp_rw [hf]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i), Finset.sum_range_id]

theorem grouping_sign : Specs.D05.M09.RealComplexBridge.Orientation.grouping_sign := by
  intro n
  unfold D05.Foundations.permutationSign
  rw [grouping_inversions]

private theorem sign_as_real (n : ℕ) :
    ((groupingPermutation n).sign : ℝ) = (-1 : ℝ)^(n*(n-1)/2) := by
  have h := grouping_sign n
  rw [D05.Foundations.PermutationSign.signIdentification] at h
  have hr := congrArg (Int.cast : ℤ → ℝ) h
  simpa using hr
theorem volume_sign : Specs.D05.M09.RealComplexBridge.Orientation.volume_sign := by
  intro V _ _ n b M _ _ f
  change f ((groupedBasis b).reindex (groupingPermutation n)) = _
  rw [Module.Basis.coe_reindex]
  rw [f.map_perm]
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ]
  simp only [Equiv.Perm.sign_symm]
  rw [show (((groupingPermutation n).sign : ℤ) : ℝ) = (-1 : ℝ)^(n*(n-1)/2) by
    exact_mod_cast sign_as_real n]
theorem convention_determinant : Specs.D05.M09.RealComplexBridge.Orientation.convention_determinant := by
  intro V _ _ n b
  rw [D05.M05.Orientation.conversion_det_basis]
  rw [volume_sign, (groupedBasis b).det_self, smul_eq_mul, mul_one]
theorem conventions_agree_iff : Specs.D05.M09.RealComplexBridge.Orientation.conventions_agree_iff := by
  intro V _ _ n b
  change (Specs.D05.M05.Orientation.classOf_value (interleavedBasis b) =
    Specs.D05.M05.Orientation.classOf_value (groupedBasis b)) ↔ _
  rw [eq_comm, D05.M05.Orientation.class_eq_iff]
  change 0 < _root_.D05.M05.determinant _ ↔ _
  rw [convention_determinant]
  constructor
  · intro h
    rcases neg_one_pow_eq_or (R := ℝ) (n*(n-1)/2) with hp | hp
    · exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp hp
    · rw [hp] at h
      norm_num at h
  · intro h
    rw [h.neg_one_pow]
    norm_num
theorem zero_orientation : Specs.D05.M09.RealComplexBridge.Orientation.zero_orientation := by
  intro V _ _ b
  constructor
  · exact (conventions_agree_iff b).mpr (by simp)
  · intro o
    induction o using Quot.ind with
    | mk c =>
      change Specs.D05.M05.Orientation.classOf_value c =
        Specs.D05.M05.Orientation.classOf_value (interleavedBasis b)
      rw [D05.M05.Orientation.zero_unique_basis c (interleavedBasis b)]

end D05.M09.RealComplexBridge.Orientation
