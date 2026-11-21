import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Spectral.LowRankFrobenius
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.MatrixData
import MathGenome.Internal.D05.M14.LowRank.LowerBound
import MathGenome.Internal.D05.M14.LowRank.Truncation

noncomputable section
open scoped BigOperators
namespace NumAnalysis206.LowRankFrobenius

section LinearMaps
variable {K V W : Type*} [RCLike K]
  [NormedAddCommGroup V] [NormedAddCommGroup W]
  [InnerProductSpace K V] [InnerProductSpace K W]
  [FiniteDimensional K V] [FiniteDimensional K W]

omit [FiniteDimensional K W] in
lemma finrank_range_add_le (S T : V →ₗ[K] W) :
    Module.finrank K (S + T).range ≤
      Module.finrank K S.range + Module.finrank K T.range := by
  have h := LinearMap.rank_add_le S T
  simpa only [LinearMap.rank, ← Module.finrank_eq_rank, ← Nat.cast_add,
    Nat.cast_le] using h

/-- Removing a map of rank at most k shifts the ordered singular values by k. -/
lemma singularValues_shift_le (T S : V →ₗ[K] W) (k j : ℕ)
    (hS : Module.finrank K S.range ≤ k) :
    T.singularValues (k + j) ≤ (T - S).singularValues j := by
  by_cases hk : k + j < Module.finrank K T.range
  · obtain ⟨d⟩ := D05.M14.Svd.exists_svd (T - S)
    have hr : Module.finrank K
        (S + D05.svdTruncation (T - S) d j).range ≤ k + j :=
      (finrank_range_add_le _ _).trans (Nat.add_le_add hS
        (D05.M14.LowRank.Truncation.rank_le (T - S) d j))
    have h := D05.M14.LowRank.LowerBound.lower_bound T
      (S + D05.svdTruncation (T - S) d j) (k + j) hk hr
    have heq : T - (S + D05.svdTruncation (T - S) d j) =
        (T - S) - D05.svdTruncation (T - S) d j := by abel
    rw [heq, D05.M14.LowRank.Truncation.error_norm] at h
    exact h
  · rw [T.singularValues_eq_zero_iff_le_finrank_range.mpr (Nat.le_of_not_gt hk)]
    exact (T - S).singularValues_nonneg j

/-- Zero padding permits summing over the full right-hand space. -/
lemma frobenius_sq_singular_sum (T : V →ₗ[K] W) :
    D05.frobeniusNorm T ^ 2 =
      ∑ i : Fin (Module.finrank K V), T.singularValues i ^ 2 := by
  classical
  rw [D05.M14.Frobenius.singular_sum]
  apply Finset.sum_of_injOn (fun i => Fin.castLE T.finrank_range_le i)
  · intro i hi j hj h
    exact Fin.castLE_injective _ h
  · intro i hi
    simp
  · intro j hj hnot
    have hjr : Module.finrank K T.range ≤ j.val := by
      by_contra hn
      exact hnot ⟨⟨j.val, Nat.lt_of_not_ge hn⟩, Finset.mem_univ _, rfl⟩
    rw [T.singularValues_eq_zero_iff_le_finrank_range.mpr hjr]
    simp
  · intro i hi
    rfl

lemma tail_lower_bound (T S : V →ₗ[K] W) (k : ℕ)
    (hS : Module.finrank K S.range ≤ k) :
    (∑ i : Fin (Module.finrank K T.range - k), T.singularValues (k + i.val) ^ 2) ≤
      D05.frobeniusNorm (T - S) ^ 2 := by
  classical
  rw [frobenius_sq_singular_sum]
  have hle : Module.finrank K T.range - k ≤ Module.finrank K V :=
    (Nat.sub_le _ _).trans T.finrank_range_le
  apply Finset.sum_le_sum_of_injOn (fun i => Fin.castLE hle i)
  · intro i hi j hj h
    exact Fin.castLE_injective _ h
  · simp
  · intro i hi
    exact (sq_le_sq₀ (T.singularValues_nonneg _) ((T - S).singularValues_nonneg _)).mpr
      (singularValues_shift_le T S k i hS)
  · intro i hi hnot
    exact sq_nonneg _

/-- Parseval for the omitted SVD coefficients gives the exact Frobenius tail. -/
lemma truncation_frobenius_sq (T : V →ₗ[K] W)
    (d : D05.SingularValueDecomposition T) (k : ℕ) :
    D05.frobeniusNorm (T - D05.svdTruncation T d k) ^ 2 =
      ∑ i : Fin (Module.finrank K T.range - k), T.singularValues (k + i.val) ^ 2 := by
  classical
  let f := fun i : Fin (Module.finrank K T.range) =>
    d.codomainBasis (Fin.castLE (Submodule.finrank_le _) i)
  have hf : D05.orthonormalFamily (F := K) f :=
    (D05.M12.Orthonormal.orthonormal_iff_mathlib f).mpr
      (d.codomainBasis.orthonormal.comp _ (Fin.castLE_injective _))
  rw [D05.M14.Frobenius.squared_basis_sum _ d.domainBasis]
  calc
    _ = ∑ j, ∑ i : Fin (Module.finrank K T.range),
        if i.val < k then 0 else T.singularValues i ^ 2 *
          ‖D05.firstInner (F := K) (d.domainBasis j)
            (d.domainBasis (Fin.castLE T.finrank_range_le i))‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [D05.M14.LowRank.Truncation.residual_sum]
      rw [D05.M12.FourierParseval.norm_sq_finite_sum f hf Finset.univ]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hik : i.val < k
      · simp [hik]
      · simp only [hik, ↓reduceIte, norm_mul, mul_pow, RCLike.norm_ofReal,
          abs_of_nonneg (T.singularValues_nonneg i)]
    _ = ∑ i : Fin (Module.finrank K T.range),
        if i.val < k then 0 else T.singularValues i ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hik : i.val < k
      · simp [hik]
      · simp only [hik, ↓reduceIte, ← Finset.mul_sum, D05.firstInner]
        rw [d.domainBasis.sum_sq_norm_inner_left,
          d.domainBasis.orthonormal.norm_eq_one]
        simp
    _ = _ := by
      symm
      apply Finset.sum_of_injOn
        (fun i : Fin (Module.finrank K T.range - k) =>
          (⟨k + i.val, by omega⟩ : Fin (Module.finrank K T.range)))
      · intro i hi j hj h
        apply Fin.ext
        have := congrArg Fin.val h
        dsimp at this
        omega
      · intro i hi
        simp
      · intro j hj hnot
        have hjk : j.val < k := by
          by_contra hn
          have hge : k ≤ j.val := Nat.le_of_not_gt hn
          apply hnot
          refine ⟨⟨j.val - k, by omega⟩, Finset.mem_univ _, ?_⟩
          apply Fin.ext
          dsimp
          omega
        simp [hjk]
      · intro i hi
        simp

end LinearMaps
open MatrixData

theorem competitor_lower_bound : Specs.NumAnalysis206.LowRankFrobenius.competitor_lower_bound := by
  intro K _ m n A B k hB
  have h := tail_lower_bound A.toEuclideanLin B.toEuclideanLin k hB
  rw [← map_sub Matrix.toEuclideanLin A B, ← frobeniusNorm_eq_D05] at h
  change (∑ i : Fin (MatrixDefinitions.rank A - k),
    A.toEuclideanLin.singularValues (k + i.val + 1 - 1) ^ 2) ≤
    MatrixDefinitions.frobeniusNorm (A - B) ^ 2
  simp only [Nat.add_sub_cancel]
  exact h

theorem residual_squared : Specs.NumAnalysis206.LowRankFrobenius.residual_squared := by
  intro K _ m n A d k
  change MatrixDefinitions.frobeniusNorm (A - MatrixDefinitions.svdTruncation A d k) ^ 2 =
    ∑ i : Fin (MatrixDefinitions.rank A - k),
      A.toEuclideanLin.singularValues (k + i.val + 1 - 1) ^ 2
  simp only [Nat.add_sub_cancel]
  rw [frobeniusNorm_eq_D05, map_sub, svdTruncation_transport]
  exact truncation_frobenius_sq A.toEuclideanLin d k

theorem best_approximation : Specs.NumAnalysis206.LowRankFrobenius.best_approximation := by
  intro K _ m n A d k
  refine ⟨?_, residual_squared A d k, ?_⟩
  · change Module.finrank K (MatrixDefinitions.svdTruncation A d k).toEuclideanLin.range ≤ k
    rw [svdTruncation_transport]
    exact D05.M14.LowRank.Truncation.rank_le A.toEuclideanLin d k
  · intro B hB
    have hs := (residual_squared A d k).trans_le (competitor_lower_bound A B k hB)
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp hs

end NumAnalysis206.LowRankFrobenius
