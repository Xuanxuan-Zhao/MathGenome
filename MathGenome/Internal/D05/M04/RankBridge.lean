import MathGenome.Internal.Specs.D05.M04.RankBridge
import MathGenome.Internal.D05.M03.Image
import MathGenome.Internal.D05.M03.CompositionRank
import MathGenome.Internal.D05.M04.MatrixOfMap

/-! K05.04.rank_bridge: the column image and row/column/map rank bridges. -/

namespace D05.M04.RankBridge

theorem mulVec_eq_column_sum : Specs.D05.M04.RankBridge.mulVec_eq_column_sum := by
  intro R _ m n A x
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Matrix.col, mul_comm]

theorem image_eq_column_span : Specs.D05.M04.RankBridge.image_eq_column_span := by
  intro R _ m n A
  exact Matrix.range_mulVecLin A

theorem mem_column_span_iff : Specs.D05.M04.RankBridge.mem_column_span_iff := by
  intro R _ m n A y
  rw [← image_eq_column_span A]
  exact LinearMap.mem_range

theorem column_rank_eq_map_rank : Specs.D05.M04.RankBridge.column_rank_eq_map_rank := by
  intro K _ m n A
  change Module.finrank K (Submodule.span K (Set.range A.col)) =
    Module.finrank K (LinearMap.range A.mulVecLin)
  rw [Matrix.range_mulVecLin]

theorem rank_eq_column_rank : Specs.D05.M04.RankBridge.rank_eq_column_rank := by
  intro K _ m n A
  exact Matrix.rank_eq_finrank_span_cols A

theorem row_rank_eq_column_rank : Specs.D05.M04.RankBridge.row_rank_eq_column_rank := by
  intro K _ m n A
  exact (Matrix.rank_eq_finrank_span_row A).symm.trans (rank_eq_column_rank A)

theorem rank_transpose : Specs.D05.M04.RankBridge.rank_transpose := by
  intro K _ m n A
  exact Matrix.rank_transpose A

theorem matrixOfMap_rank : Specs.D05.M04.RankBridge.matrixOfMap_rank := by
  intro K V W _ _ _ _ _ n m b c T
  change (LinearMap.toMatrix b c T).rank = Module.finrank K (LinearMap.range T)
  rw [Matrix.rank_eq_finrank_range_toLin _ c b, Matrix.toLin_toMatrix]

theorem mapOfMatrix_rank : Specs.D05.M04.RankBridge.mapOfMatrix_rank := by
  intro K V W _ _ _ _ _ n m b c A
  exact Matrix.rank_eq_finrank_range_toLin A c b

end D05.M04.RankBridge
