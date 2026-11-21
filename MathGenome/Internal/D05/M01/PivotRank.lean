import MathGenome.Internal.Specs.D05.M01.PivotRank
import MathGenome.Internal.D05.M01.Echelon
import MathGenome.Internal.D05.M01.RowOps
import MathGenome.Internal.D05.M04.RankBridge
import MathGenome.Internal.D05.M02.Basis
import Mathlib.LinearAlgebra.Matrix.Echelon.Pivot
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace D05.M01.PivotRank
open PivotRankData
open scoped BigOperators
universe u
variable {K : Type u} [Field K] {m n : ℕ}

theorem pivotColumn_isLeadingEntry (R : Matrix (Fin m) (Fin n) K) (i : PivotRow R) :
    R.IsLeadingEntry i.val (pivotColumn R i) :=
  Classical.choose_spec (Matrix.row_ne_zero_iff_exists_isLeadingEntry.mp i.property)

theorem pivotColumn_eq_iff (R : Matrix (Fin m) (Fin n) K) (i : PivotRow R) (c : Fin n) :
    pivotColumn R i = c ↔ R.IsLeadingEntry i.val c := by
  constructor
  · intro h
    simpa only [← h] using pivotColumn_isLeadingEntry R i
  · exact fun h => (pivotColumn_isLeadingEntry R i).unique h

theorem pivotColumn_strictMono (R : Matrix (Fin m) (Fin n) K) (hR : R.IsRowEchelon) :
    StrictMono (pivotColumn R) := by
  intro i j hij
  exact ((Echelon.rowEchelon_iff R).mp hR).2 i.val j.val _ _ hij
    (pivotColumn_isLeadingEntry R i) (pivotColumn_isLeadingEntry R j)

theorem pivot_columns_count : Specs.D05.M01.PivotRank.pivot_columns_count := by
  intro K _ m n R hR
  let e : PivotRow R ≃ {c : Fin n // ∃ i, R.IsLeadingEntry i c} :=
    Equiv.ofBijective
      (fun i => ⟨pivotColumn R i, i.val, pivotColumn_isLeadingEntry R i⟩) (by
        constructor
        · intro i j hij
          exact (pivotColumn_strictMono R hR).injective (congrArg Subtype.val hij)
        · rintro ⟨c, i, hi⟩
          refine ⟨⟨i, hi.row_ne_zero⟩, ?_⟩
          exact Subtype.ext ((pivotColumn_eq_iff R _ c).mpr hi))
  exact (Nat.card_congr e).symm

theorem echelon_rank : Specs.D05.M01.PivotRank.echelon_rank := by
  intro K _ m n R hR
  classical
  let l : Fin m → WithTop (Fin n) := fun i =>
    if hi : R i = 0 then ⊤ else ↑(pivotColumn R ⟨i, hi⟩)
  have hp : R.IsPivotedBy l := by
    refine ⟨hR, ?_⟩
    intro i
    by_cases hi : R i = 0
    · simp only [l, dite_eq_left hi]
      exact ⟨fun j _ => congrFun hi j, fun c hc => (WithTop.top_ne_coe hc).elim⟩
    · simp only [l, dite_eq_right hi]
      refine ⟨fun j hj => (pivotColumn_isLeadingEntry R ⟨i, hi⟩).1 j
        (WithTop.coe_lt_coe.mp hj), ?_⟩
      intro c hc
      have hc' : pivotColumn R ⟨i, hi⟩ = c := WithTop.coe_injective hc
      simpa only [hc'] using (pivotColumn_isLeadingEntry R ⟨i, hi⟩).2
  rw [hp.rank_eq]
  simp [l, pivotCount, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem echelon_row_column_rank : Specs.D05.M01.PivotRank.echelon_row_column_rank := by
  intro K _ m n R hR
  rw [← echelon_rank R hR]
  exact ⟨Matrix.rank_eq_finrank_span_row R, M04.RankBridge.rank_eq_column_rank R⟩

theorem pivot_columns_independent : Specs.D05.M01.PivotRank.pivot_columns_independent := by
  intro K _ m n R hR
  classical
  let B : Matrix (PivotRow R) (PivotRow R) K :=
    R.submatrix Subtype.val (pivotColumn R)
  have ht : B.IsUpperTriangular := by
    intro i j hji
    exact (pivotColumn_isLeadingEntry R i).1 _ (pivotColumn_strictMono R hR hji)
  have hd : B.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular ht]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => (pivotColumn_isLeadingEntry R i).2)
  have hli : LinearIndependent K B.col :=
    Matrix.linearIndependent_col_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hd))
  let f : (Fin m → K) →ₗ[K] (PivotRow R → K) :=
    LinearMap.funLeft K K Subtype.val
  exact LinearIndependent.of_comp f hli

/-- A full-size independent subfamily of the columns spans the whole column space. -/
theorem span_columns_of_independent_card {ι : Type*} [Fintype ι]
    (A : Matrix (Fin m) (Fin n) K) (c : ι → Fin n)
    (hli : LinearIndependent K (fun i => A.col (c i)))
    (hc : Fintype.card ι = A.rank) :
    Submodule.span K (Set.range (fun i => A.col (c i))) =
      Submodule.span K (Set.range A.col) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · exact Submodule.span_mono (Set.range_comp_subset_range c A.col)
  · rw [finrank_span_eq_card hli, hc, ← Matrix.rank_eq_finrank_span_cols]

theorem pivot_columns_span : Specs.D05.M01.PivotRank.pivot_columns_span := by
  intro K _ m n R hR
  classical
  exact span_columns_of_independent_card R (pivotColumn R) (pivot_columns_independent R hR)
    (by simpa [pivotCount, Nat.card_eq_fintype_card] using (echelon_rank R hR).symm)

theorem original_rank : Specs.D05.M01.PivotRank.original_rank := by
  intro K _ m n A R E hE hRA hR
  have hr : R.rank = A.rank := by
    rw [hRA]
    exact Matrix.rank_mul_eq_right_of_isUnit_det E A ((Matrix.isUnit_iff_isUnit_det E).mp hE)
  rw [← echelon_rank R hR, hr]
  exact ⟨Matrix.rank_eq_finrank_span_row A, M04.RankBridge.rank_eq_column_rank A⟩

theorem original_pivot_columns_basis :
    Specs.D05.M01.PivotRank.original_pivot_columns_basis := by
  intro K _ m n A R E hE hRA hR
  classical
  have hcols : (fun i : PivotRow R => R.col (pivotColumn R i)) =
      E.mulVecLin ∘ (fun i => A.col (pivotColumn R i)) := by
    funext i r
    simp [hRA, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col]
  have hli : LinearIndependent K (fun i : PivotRow R => A.col (pivotColumn R i)) :=
    LinearIndependent.of_comp E.mulVecLin (hcols ▸ pivot_columns_independent R hR)
  have hc : Fintype.card (PivotRow R) = A.rank := by
    rw [M04.RankBridge.rank_eq_column_rank A]
    simpa [pivotCount, Nat.card_eq_fintype_card] using (original_rank A R E hE hRA hR).2
  have hs := span_columns_of_independent_card A (pivotColumn R) hli hc
  let v : PivotRow R → Submodule.span K (Set.range A.col) :=
    fun i => ⟨A.col (pivotColumn R i), Submodule.subset_span (Set.mem_range_self _)⟩
  have hv : LinearIndependent K v := by
    exact LinearIndependent.of_comp (Submodule.subtype _) hli
  have ht : Submodule.span K (Set.range v) = ⊤ := by
    apply Submodule.map_injective_of_injective (Submodule.subtype_injective _)
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    rw [← Set.range_comp]
    change Submodule.span K (Set.range (fun i : PivotRow R => A.col (pivotColumn R i))) = _
    exact hs
  exact ⟨Module.Basis.mk hv ht.ge, fun i => by simp [Module.Basis.mk_apply, v]⟩

theorem row_operations_multiplier : Specs.D05.M01.PivotRank.row_operations_multiplier := by
  intro K _ m n ops
  induction ops with
  | nil =>
    intro A
    exact ⟨1, isUnit_one, (Matrix.one_mul A).symm⟩
  | cons op ops ih =>
    intro A
    obtain ⟨E, hE, he⟩ := ih (RowOps.applyOp op A)
    refine ⟨E * RowOps.elementaryMatrix op, hE.mul (RowOps.elementary_isUnit op), ?_⟩
    change ops.foldl (fun B op => RowOps.applyOp op B) (RowOps.applyOp op A) = _
    change ops.foldl (fun B op => RowOps.applyOp op B) (RowOps.applyOp op A) = _ at he
    rw [he, Matrix.mul_assoc, RowOps.elementary_mul]

/-- Assemble the rank and original-column conclusions for an actual row-operation
sequence, without asking for an independently supplied decomposition certificate. -/
theorem pivots_and_original_columns : Specs.D05.M01.PivotRank.pivots_and_original_columns := by
  intro K _ m n ops A
  dsimp only
  intro hR
  obtain ⟨E, hE, he⟩ := row_operations_multiplier ops A
  exact ⟨(original_rank A _ E hE he hR).1,
    (original_rank A _ E hE he hR).2,
    original_pivot_columns_basis A _ E hE he hR⟩

end D05.M01.PivotRank
