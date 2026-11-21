import MathGenome.Internal.Specs.D05.M14.LowRank
import MathGenome.Internal.D05.M14.LowRank.Truncation
import MathGenome.Internal.D05.M14.LowRank.LowerBound

/-! Best approximation of bounded rank in the operator norm.
The two prerequisites supply the exact truncation error and the lower bound
for every competing map. Their combination also covers k=0 and zero spaces.
-/

noncomputable section
namespace D05.M14.LowRank

theorem optimality : Specs.D05.M14.LowRank.optimality := by
  intro F V W _ _ _ _ _ _ _ T d k S hS
  by_cases hk : k < Module.finrank F T.range
  · rw [Truncation.error_norm T d k]
    exact LowerBound.lower_bound T S k hk hS
  · rw [(Truncation.error_of_rank_le T d k (Nat.le_of_not_gt hk)).2]
    exact D05.M14.OperatorNorm.nonneg (T - S)

theorem best_approximation : Specs.D05.M14.LowRank.best_approximation := by
  intro F V W _ _ _ _ _ _ _ T d k
  refine ⟨Truncation.rank_le T d k, optimality T d k, ?_⟩
  by_cases hk : k < Module.finrank F T.range
  · rw [if_pos hk]
    exact Truncation.error_of_lt_rank T d k hk
  · rw [if_neg hk]
    exact (Truncation.error_of_rank_le T d k (Nat.le_of_not_gt hk)).2

theorem minimum_error : Specs.D05.M14.LowRank.minimum_error := by
  intro F V W _ _ _ _ _ _ _ T k
  obtain ⟨d⟩ := D05.M14.Svd.exists_svd T
  obtain ⟨hrank, hbest, herr⟩ := best_approximation T d k
  refine ⟨⟨D05.svdTruncation T d k, hrank, herr⟩, ?_⟩
  rintro ε ⟨S, hS, rfl⟩
  rw [← herr]
  exact hbest S hS

end D05.M14.LowRank
