import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Spectral.LowRankOperator
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.MatrixData
import MathGenome.Internal.D05.M14.LowRank

/-! Matrix form of W41. The library theorem acts on the associated Euclidean
linear maps; all transports below preserve the actual rank and induced norm. -/

noncomputable section

namespace NumAnalysis206.LowRankOperator
open MatrixData

theorem best_approximation : Specs.NumAnalysis206.LowRankOperator.best_approximation := by
  intro K _ m n A d k
  have hrank := D05.M14.LowRank.Truncation.rank_le A.toEuclideanLin d k
  have herr := D05.M14.LowRank.Truncation.error_norm A.toEuclideanLin d k
  refine ⟨?_, ?_, ?_⟩
  · change Module.finrank K (svdTruncation A d k).toEuclideanLin.range ≤ k
    rw [svdTruncation_transport]
    exact hrank
  · rw [operatorNorm_eq_D05, map_sub, svdTruncation_transport]
    simpa only [NumAnalysis206.MatrixDefinitions.singularValue, Nat.add_sub_cancel] using herr
  · intro B hB
    have hbest := D05.M14.LowRank.optimality A.toEuclideanLin d k B.toEuclideanLin hB
    rw [herr] at hbest
    rw [operatorNorm_eq_D05, map_sub]
    simpa only [NumAnalysis206.MatrixDefinitions.singularValue, Nat.add_sub_cancel] using hbest

theorem minimum_error : Specs.NumAnalysis206.LowRankOperator.minimum_error := by
  intro K _ m n A k
  obtain ⟨d⟩ := D05.M14.Svd.exists_svd A.toEuclideanLin
  obtain ⟨hrank, herr, hlower⟩ := best_approximation A d k
  refine ⟨⟨svdTruncation A d k, hrank, herr⟩, ?_⟩
  rintro ε ⟨B, hB, rfl⟩
  exact hlower B hB

end NumAnalysis206.LowRankOperator
