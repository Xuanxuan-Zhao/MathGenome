import MathGenome.Internal.Specs.D05.M05.Adjugate.RankCases
import MathGenome.Internal.D05.M05.Adjugate.RankMinors
import MathGenome.Internal.D05.M05.Adjugate
import MathGenome.Internal.D05.M05.DetInvertible
import MathGenome.Internal.D05.M03.RankNullity

/-! Field rank cases for the adjugate. The singular cases are proved from
nonzero minors and containment of the adjugate image in the kernel. -/

noncomputable section

namespace D05.M05.Adjugate.RankCases

open _root_.D05.M05

/-- Full square rank implies nonzero determinant, using the invertibility
criterion, without any determinant formula for the adjugate. -/
theorem det_ne_zero_of_full_rank {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA : A.rank = n) : determinant A ≠ 0 := by
  have hs : Function.Surjective A.mulVec :=
    Matrix.mulVec_surjective_iff_rank_eq_card.mpr (by simpa using hA)
  have hu := Matrix.mulVec_surjective_iff_isUnit.mp hs
  rw [DetDefinition.matrix_det_bridge]
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp hu)

/-- Any selection of all but one index factors through an ordered deletion.
The factor need not be assumed to be a permutation for the rank argument. -/
theorem embedding_factors_through_deletion {n : ℕ} (e : Fin n ↪ Fin (n + 1)) :
    ∃ (i : Fin (n + 1)) (r : Fin n → Fin n), e = i.succAbove ∘ r := by
  classical
  have hnot : ¬ Function.Surjective e := by
    intro hs
    have hc := Fintype.card_le_of_surjective e hs
    simp only [Fintype.card_fin] at hc
    omega
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  have hex : ∀ a, ∃ b, i.succAbove b = e a := by
    intro a
    apply Fin.exists_succAbove_eq
    exact fun h => hi ⟨a, h⟩
  choose r hr using hex
  exact ⟨i, r, funext fun a => (hr a).symm⟩

/-- A nonzero minor of size n in an (n+1)-square matrix yields a nonzero
ordered deleted minor. This includes n=0 and its empty determinant. -/
theorem exists_nonzero_deleted_minor {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hA : A.rank = n) :
    ∃ i j, determinant (deletedMatrix A i j) ≠ 0 := by
  classical
  have hm := RankMinors.exists_rank_minor A
  rw [hA] at hm
  obtain ⟨rows, cols, hdet⟩ := hm
  obtain ⟨i, r, hr⟩ := embedding_factors_through_deletion rows
  obtain ⟨j, c, hc⟩ := embedding_factors_through_deletion cols
  refine ⟨i, j, det_ne_zero_of_full_rank _ ?_⟩
  have hfull : (A.submatrix rows cols).rank = n := by
    rw [DetDefinition.matrix_det_bridge] at hdet
    simpa using Matrix.rank_of_det_ne_zero hdet
  have heq : A.submatrix rows cols = (deletedMatrix A i j).submatrix r c := by
    ext a b
    change A (rows a) (cols b) = A (i.succAbove (r a)) (j.succAbove (c b))
    rw [hr, hc]
    rfl
  have hle := Matrix.rank_submatrix_le (deletedMatrix A i j) r c
  rw [← heq, hfull] at hle
  exact Nat.le_antisymm (Matrix.rank_le_width _) hle

/-- The product identity places the adjugate range in the kernel whenever
A is singular. -/
theorem range_adjugate_le_ker {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hdet : determinant A = 0) :
    LinearMap.range (_root_.D05.M05.adjugate A).mulVecLin ≤ LinearMap.ker A.mulVecLin := by
  rw [LinearMap.range_le_ker_iff, ← Matrix.mulVecLin_mul]
  rw [Adjugate.mul_adjugate A, hdet, zero_smul, Matrix.mulVecLin_zero]

/-- A nonzero entry gives a nonzero singleton minor, hence positive rank. -/
theorem one_le_rank_of_entry_ne_zero {K : Type*} [Field K] {m n : ℕ}
    (B : Matrix (Fin m) (Fin n) K) (i : Fin m) (j : Fin n) (h : B i j ≠ 0) :
    1 ≤ B.rank := by
  let rows : Fin 1 ↪ Fin m := ⟨fun _ => i, fun _ _ _ => Subsingleton.elim _ _⟩
  let cols : Fin 1 ↪ Fin n := ⟨fun _ => j, fun _ _ _ => Subsingleton.elim _ _⟩
  apply RankMinors.minor_size_le_rank B rows cols
  rw [DetDefinition.matrix_det_bridge, Matrix.det_fin_one]
  exact h

theorem full_rank : Specs.D05.M05.Adjugate.RankCases.full_rank := by
  intro K _ n _ A hA
  classical
  have hd := det_ne_zero_of_full_rank A hA
  have hp : (A * _root_.D05.M05.adjugate A).rank = n := by
    rw [Adjugate.mul_adjugate A,
      Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hd),
      Matrix.rank_one, Fintype.card_fin]
  have hle := Matrix.rank_mul_le_right A (_root_.D05.M05.adjugate A)
  rw [hp] at hle
  exact Nat.le_antisymm (Matrix.rank_le_width _) hle

theorem corank_one : Specs.D05.M05.Adjugate.RankCases.corank_one := by
  intro K _ n hn A hA
  classical
  cases n with
  | zero => omega
  | succ n =>
    simp only [Nat.succ_sub_one] at hA
    have hd : determinant A = 0 := by
      by_contra hne
      have hf := Matrix.rank_of_det_ne_zero
        (show A.det ≠ 0 by rwa [← DetDefinition.matrix_det_bridge])
      simp only [Fintype.card_fin] at hf
      omega
    obtain ⟨i, j, hij⟩ := exists_nonzero_deleted_minor A hA
    have he : _root_.D05.M05.adjugate A j i ≠ 0 := by
      rw [Adjugate.cofactor_entry]
      unfold cofactor
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hij
    have hlo := one_le_rank_of_entry_ne_zero (_root_.D05.M05.adjugate A) j i he
    have hnull : n + 1 = Module.finrank K (LinearMap.ker A.mulVecLin) + A.rank := by
      simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Matrix.rank]
        using D05.M03.RankNullity.rank_nullity A.mulVecLin
    have hker : Module.finrank K (LinearMap.ker A.mulVecLin) = 1 := by omega
    have hup : (_root_.D05.M05.adjugate A).rank ≤ Module.finrank K (LinearMap.ker A.mulVecLin) :=
      Submodule.finrank_mono (range_adjugate_le_ker A hd)
    omega

/-- All cofactors vanish below corank one. The size restriction prevents
truncated subtraction from including the one-dimensional zero matrix. -/
theorem adjugate_eq_zero_of_corank_at_least_two {K : Type*} [Field K] {n : ℕ}
    (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) K) (hA : A.rank ≤ n - 2) :
    _root_.D05.M05.adjugate A = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    have hlt : A.rank < n := by omega
    ext i j
    rw [Adjugate.cofactor_entry]
    unfold cofactor deletedMatrix
    have hminor := RankMinors.larger_minors_vanish A hlt j.succAboveEmb i.succAboveEmb
    change determinant (A.submatrix j.succAbove i.succAbove) = 0 at hminor
    rw [hminor, mul_zero]
    rfl

theorem corank_at_least_two : Specs.D05.M05.Adjugate.RankCases.corank_at_least_two := by
  intro K _ n hn A hA
  rw [adjugate_eq_zero_of_corank_at_least_two hn A hA, Matrix.rank_zero]

theorem singleton_zero_adjugate : Specs.D05.M05.Adjugate.RankCases.singleton_zero_adjugate := by
  intro K _
  exact Adjugate.singleton_adjugate _

theorem singleton_zero_rank : Specs.D05.M05.Adjugate.RankCases.singleton_zero_rank := by
  intro K _
  rw [singleton_zero_adjugate, Matrix.rank_one, Fintype.card_fin]

end D05.M05.Adjugate.RankCases
