import MathGenome.Internal.Specs.D05.M01.InverseAlgorithm
import MathGenome.Internal.D05.M01.Elimination
import MathGenome.Internal.D05.M01.PivotRank
import MathGenome.Internal.D05.M04.InverseMatrix
import Mathlib.Order.Preorder.Finite

/-! Computing inverses by simultaneous elementary row reduction,
K05.01.inverse_algorithm. All lists here are the actual permitted operations. -/
namespace D05.M01.InverseAlgorithm

open InverseAlgorithmData Elimination RowOps PivotRankData
universe u
variable {K : Type u} [Field K] {m n p : ℕ}

theorem block_left : Specs.D05.M01.InverseAlgorithm.block_left := by
  intro K m n p A C i j
  exact Fin.append_left (A i) (C i) j

theorem block_right : Specs.D05.M01.InverseAlgorithm.block_right := by
  intro K m n p A C i j
  exact Fin.append_right (A i) (C i) j

/-- Left multiplication respects horizontal concatenation of ordered blocks. -/
theorem mul_blockAugment (E : Matrix (Fin m) (Fin m) K)
    (A : Matrix (Fin m) (Fin n) K) (C : Matrix (Fin m) (Fin p) K) :
    E * blockAugment A C = blockAugment (E * A) (E * C) := by
  ext i j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [Matrix.mul_apply, blockAugment]
  · simp [Matrix.mul_apply, blockAugment]

omit [Field K] in
/-- Equality of augmentations recovers both individual blocks. -/
theorem blockAugment_inj {A A' : Matrix (Fin m) (Fin n) K}
    {C C' : Matrix (Fin m) (Fin p) K}
    (h : blockAugment A C = blockAugment A' C') : A = A' ∧ C = C' := by
  constructor
  · ext i j
    simpa [blockAugment] using congrArg (fun M => M i (Fin.castAdd p j)) h
  · ext i j
    simpa [blockAugment] using congrArg (fun M => M i (Fin.natAdd n j)) h

theorem identity_block_reduced : Specs.D05.M01.InverseAlgorithm.identity_block_reduced := by
  intro K _ n B
  let C := blockAugment (1 : Matrix (Fin n) (Fin n) K) B
  have hp : ∀ i : Fin n, C.IsLeadingEntry i (Fin.castAdd n i) := by
    intro i
    refine ⟨?_, ?_⟩
    · intro j
      refine Fin.addCases (fun j hj => ?_) (fun j hj => ?_) j
      · have hji : j < i := hj
        simp [C, blockAugment, ne_of_gt hji]
      · have hjval : n + j.val < i.val := hj
        omega
    · simp [C, blockAugment]
  apply (Echelon.reducedRowEchelon_iff C).mpr
  refine ⟨(Echelon.rowEchelon_iff C).mpr ⟨?_, ?_⟩, ?_⟩
  · intro i k hik hz
    exact ((hp i).row_ne_zero hz).elim
  · intro i k c d hik hc hd
    rw [hc.unique (hp i), hd.unique (hp k)]
    exact hik
  · intro i c hc
    rw [hc.unique (hp i)]
    refine ⟨?_, ?_⟩
    · simp [C, blockAugment]
    · intro k hki
      simp [C, blockAugment, hki]

/-- Executing a list on an augmentation executes that very same list on
both blocks, so no separately chosen multiplier is needed. -/
theorem applyOps_blockAugment (ops : List (RowOperation K m))
    (A : Matrix (Fin m) (Fin n) K) (C : Matrix (Fin m) (Fin p) K) :
    applyOps ops (blockAugment A C) =
      blockAugment (applyOps ops A) (applyOps ops C) := by
  induction ops generalizing A C with
  | nil => rfl
  | cons op ops ih =>
    have hop : RowOpsSpec.applyOpValue op (blockAugment A C) =
        blockAugment (RowOpsSpec.applyOpValue op A) (RowOpsSpec.applyOpValue op C) := by
      cases op <;> ext i j <;>
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [blockAugment, RowOpsSpec.applyOpValue]
    change applyOps ops (RowOpsSpec.applyOpValue op (blockAugment A C)) = _
    rw [hop, ih]
    rfl

theorem augmented_multiplier : Specs.D05.M01.InverseAlgorithm.augmented_multiplier := by
  intro K _ n ops A
  obtain ⟨E, hE, he⟩ := PivotRank.row_operations_multiplier ops
    (blockAugment A (1 : Matrix (Fin n) (Fin n) K))
  refine ⟨E, hE, ?_⟩
  change applyOps ops (blockAugment A 1) = E * blockAugment A 1 at he
  simpa only [mul_blockAugment, Matrix.mul_one] using he

theorem successful_run : Specs.D05.M01.InverseAlgorithm.successful_run := by
  intro K _ n ops A B h
  obtain ⟨E, _, he⟩ := augmented_multiplier ops A
  obtain ⟨hEA, hEB⟩ := blockAugment_inj (he.symm.trans h)
  have hBA : B * A = 1 := hEB ▸ hEA
  have hAB := M04.InverseMatrix.left_inverse_is_right A B hBA
  exact ⟨⟨⟨A, B, hAB, hBA⟩, rfl⟩, hBA, hAB,
    (Matrix.inv_eq_left_inv hBA).symm⟩

theorem reduced_unit_eq_one : Specs.D05.M01.InverseAlgorithm.reduced_unit_eq_one := by
  intro K _ n R hR hunit
  classical
  have hne : ∀ i, R i ≠ 0 :=
    (Matrix.linearIndependent_row_iff_isUnit.mpr hunit).ne_zero
  let f : Fin n → Fin n := fun i => pivotColumn R ⟨i, hne i⟩
  have hf : StrictMono f := fun i j hij =>
    PivotRank.pivotColumn_strictMono R hR.isRowEchelon hij
  have hfid : f = id := hf.eq_id
  have hp : ∀ i, R.IsLeadingEntry i i := by
    intro i
    have hi := PivotRank.pivotColumn_isLeadingEntry R ⟨i, hne i⟩
    change R.IsLeadingEntry i (f i) at hi
    simpa only [hfid, id_eq] using hi
  ext i j
  by_cases hij : i = j
  · subst j
    simpa using hR.eq_one (hp i)
  · simpa [Matrix.one_apply, hij] using
      hR.eq_zero_of_ne_of_isLeadingEntry hij (hp j)

/-- The accumulated multiplier acts on the coefficient block as well. -/
theorem operations_multiplier (ops : List (RowOperation K n))
    (A : Matrix (Fin n) (Fin n) K) :
    ∃ E : Matrix (Fin n) (Fin n) K, IsUnit E ∧ applyOps ops A = E * A :=
  PivotRank.row_operations_multiplier ops A

theorem reduced_left_iff : Specs.D05.M01.InverseAlgorithm.reduced_left_iff := by
  intro K _ n ops A hR
  obtain ⟨E, hE, he⟩ := operations_multiplier ops A
  constructor
  · intro h
    have hEA : E * A = 1 := he.symm.trans h
    exact ⟨⟨A, E, M04.InverseMatrix.left_inverse_is_right A E hEA, hEA⟩, rfl⟩
  · intro hA
    exact reduced_unit_eq_one _ hR (he ▸ hE.mul hA)

theorem inverse_by_reduction : Specs.D05.M01.InverseAlgorithm.inverse_by_reduction := by
  intro K _ n A hA
  obtain ⟨ops, hR⟩ := Elimination.exists_reduced A
  have hleft := (reduced_left_iff ops A hR).mpr hA
  obtain ⟨E, _, he⟩ := augmented_multiplier ops A
  -- Extract the left block from the same augmented sequence, rather than
  -- choosing another multiplier for it.
  have hmul : applyOps ops A = E * A :=
    (blockAugment_inj ((applyOps_blockAugment ops A 1).symm.trans he)).1
  have hEA : E * A = 1 := hmul.symm.trans hleft
  have hEinv : E = A⁻¹ := (Matrix.inv_eq_left_inv hEA).symm
  refine ⟨ops, hleft, ?_⟩
  rw [hEA, hEinv] at he
  exact he

theorem inverse_algorithm : Specs.D05.M01.InverseAlgorithm.inverse_algorithm := by
  intro K _ n A B
  constructor
  · rintro ⟨ops, h⟩
    have hs := successful_run ops A B h
    exact ⟨hs.1, hs.2.2.2⟩
  · rintro ⟨hA, rfl⟩
    obtain ⟨ops, _, h⟩ := inverse_by_reduction A hA
    exact ⟨ops, h⟩

theorem missing_pivot : Specs.D05.M01.InverseAlgorithm.missing_pivot := by
  intro K _ n ops A hR ⟨c, hc⟩
  classical
  let R := applyOps ops A
  have hlt : Fintype.card (PivotRow R) < Fintype.card (Fin n) :=
    Fintype.card_lt_of_injective_not_surjective (pivotColumn R)
      (PivotRank.pivotColumn_strictMono R hR).injective (by
        intro hs
        obtain ⟨i, hi⟩ := hs c
        exact hc i.val ((PivotRank.pivotColumn_eq_iff R i c).mp hi))
  have hrankR : R.rank < n := by
    rw [PivotRank.echelon_rank R hR]
    simpa only [pivotCount, Nat.card_eq_fintype_card, Fintype.card_fin] using hlt
  obtain ⟨E, hE, he⟩ := operations_multiplier ops A
  have hrank : R.rank = A.rank := by
    rw [show R = E * A from he]
    exact Matrix.rank_mul_eq_right_of_isUnit_det E A
      ((Matrix.isUnit_iff_isUnit_det E).mp hE)
  have hltA : A.rank < n := hrank ▸ hrankR
  refine ⟨hltA, fun hA => ?_⟩
  have := Matrix.rank_of_isUnit A hA
  simp only [Fintype.card_fin] at this
  omega

theorem empty_reduction : Specs.D05.M01.InverseAlgorithm.empty_reduction := by
  intro K _ A
  have hA : A = 1 := Subsingleton.elim _ _
  refine ⟨hA ▸ isUnit_one, ?_, ?_⟩
  · exact hA
  · exact Subsingleton.elim _ _

end D05.M01.InverseAlgorithm
