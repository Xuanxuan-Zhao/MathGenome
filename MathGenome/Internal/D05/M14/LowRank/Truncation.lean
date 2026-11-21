import MathGenome.Internal.Specs.D05.M14.LowRank.Truncation
import MathGenome.Internal.D05.M14.Svd
import MathGenome.Internal.D05.M14.OperatorNorm
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The truncated SVD and its exact error, including empty dimensions. -/
noncomputable section
namespace D05.M14.LowRank.Truncation
open scoped BigOperators

abbrev truncation : Specs.D05.M14.LowRank.Truncation.truncation_type :=
  @D05.svdTruncation

theorem apply_formula : Specs.D05.M14.LowRank.Truncation.apply_formula := by
  intro F V W _ _ _ _ _ _ _ T d k v
  rfl

universe u v w
variable {F : Type u} {V : Type v} {W : Type w} [RCLike F]
  [NormedAddCommGroup V] [NormedAddCommGroup W]
  [InnerProductSpace F V] [InnerProductSpace F W]
  [FiniteDimensional F V] [FiniteDimensional F W]

/-- Writing a prefix as a sum over all positive singular indices. -/
theorem prefix_sum (T : V →ₗ[F] W) (d : D05.SingularValueDecomposition T)
    (k : ℕ) (v : V) :
    D05.svdTruncation T d k v =
      ∑ i : Fin (Module.finrank F T.range),
        if i.val < k then
          ((T.singularValues i : F) *
            D05.firstInner v (d.domainBasis (Fin.castLE T.finrank_range_le i))) •
            d.codomainBasis (Fin.castLE (Submodule.finrank_le _) i)
        else 0 := by
  classical
  unfold D05.svdTruncation
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_of_injOn (fun i => Fin.castLE (min_le_right k _) i)
  · intro i hi j hj h
    exact Fin.castLE_injective _ h
  · intro i hi
    simp
  · intro j hj hnot
    have h : ¬j.val < k := by
      intro hjk
      exact hnot ⟨⟨j.val, lt_min hjk j.isLt⟩, Finset.mem_univ _, rfl⟩
    simp [h]
  · intro i hi
    simp only [Fin.val_castLE]
    rw [ite_eq_left (lt_of_lt_of_le i.isLt (min_le_left _ _))]

theorem rank_le : Specs.D05.M14.LowRank.Truncation.rank_le := by
  intro F V W _ _ _ _ _ _ _ T d k
  classical
  let f := fun i : Fin (min k (Module.finrank F T.range)) =>
    d.codomainBasis (Fin.castLE (Submodule.finrank_le _)
      (Fin.castLE (min_le_right k _) i))
  have h : (D05.svdTruncation T d k).range ≤ Submodule.span F (Set.range f) := by
    rintro w ⟨v, rfl⟩
    rw [apply_formula]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact (Submodule.finrank_mono h).trans
    ((finrank_range_le_card (R := F) f).trans (by simpa using (min_le_left k (Module.finrank F T.range))))

theorem eq_self_of_rank_le : Specs.D05.M14.LowRank.Truncation.eq_self_of_rank_le := by
  intro F V W _ _ _ _ _ _ _ T d k hk
  ext v
  rw [prefix_sum, Svd.expansion T d v]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ite_eq_left (lt_of_lt_of_le i.isLt hk)]

/-- The error retains precisely the omitted SVD terms. -/
theorem residual_sum (T : V →ₗ[F] W) (d : D05.SingularValueDecomposition T)
    (k : ℕ) (v : V) :
    (T - D05.svdTruncation T d k) v =
      ∑ i : Fin (Module.finrank F T.range),
        ((if i.val < k then 0 else (T.singularValues i : F) *
          D05.firstInner v (d.domainBasis (Fin.castLE T.finrank_range_le i)))) •
          d.codomainBasis (Fin.castLE (Submodule.finrank_le _) i) := by
  classical
  change T v - D05.svdTruncation T d k v = _
  rw [prefix_sum, Svd.expansion T d v, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

/-- The Bessel estimate for the omitted coefficients. -/
theorem residual_norm_le (T : V →ₗ[F] W) (d : D05.SingularValueDecomposition T)
    (k : ℕ) (v : V) :
    ‖(T - D05.svdTruncation T d k) v‖ ≤ T.singularValues k * ‖v‖ := by
  classical
  let e := fun i : Fin (Module.finrank F T.range) =>
    d.domainBasis (Fin.castLE T.finrank_range_le i)
  let f := fun i : Fin (Module.finrank F T.range) =>
    d.codomainBasis (Fin.castLE (Submodule.finrank_le _) i)
  have he : D05.orthonormalFamily (F := F) e :=
    (D05.M12.Orthonormal.orthonormal_iff_mathlib e).mpr
      (d.domainBasis.orthonormal.comp _ (Fin.castLE_injective _))
  have hf : D05.orthonormalFamily (F := F) f :=
    (D05.M12.Orthonormal.orthonormal_iff_mathlib f).mpr
      (d.codomainBasis.orthonormal.comp _ (Fin.castLE_injective _))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (T.singularValues_nonneg k)
    (norm_nonneg v))).mp
  rw [mul_pow]
  calc
    ‖(T - D05.svdTruncation T d k) v‖ ^ 2 =
        ∑ i : Fin (Module.finrank F T.range),
          ‖(if i.val < k then 0 else (T.singularValues i : F) *
            D05.firstInner v (e i))‖ ^ 2 := by
      rw [residual_sum]
      exact D05.M12.FourierParseval.norm_sq_finite_sum f hf Finset.univ _
    _ ≤ ∑ i : Fin (Module.finrank F T.range),
        T.singularValues k ^ 2 * ‖D05.firstInner (F := F) v (e i)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs with hik
      · simp only [norm_zero, zero_pow (by decide : 2 ≠ 0)]
        positivity
      · rw [norm_mul, mul_pow, RCLike.norm_ofReal,
          abs_of_nonneg (T.singularValues_nonneg i)]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact (sq_le_sq₀ (T.singularValues_nonneg i) (T.singularValues_nonneg k)).mpr
          (T.singularValues_antitone (Nat.le_of_not_gt hik))
    _ = T.singularValues k ^ 2 *
        ∑ i : Fin (Module.finrank F T.range),
          ‖D05.firstInner (F := F) v (e i)‖ ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ T.singularValues k ^ 2 * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_left
        (D05.M12.FourierParseval.bessel_finite_family e he v) (sq_nonneg _)

/-- Equality in the tail bound at the first omitted right singular vector. -/
theorem residual_attains (T : V →ₗ[F] W) (d : D05.SingularValueDecomposition T)
    (k : ℕ) (hk : k < Module.finrank F T.range) :
    let e := d.domainBasis (Fin.castLE T.finrank_range_le ⟨k, hk⟩)
    ‖e‖ = 1 ∧ ‖(T - D05.svdTruncation T d k) e‖ = T.singularValues k := by
  classical
  dsimp only
  refine ⟨d.domainBasis.orthonormal.norm_eq_one _, ?_⟩
  have hz : D05.svdTruncation T d k
      (d.domainBasis (Fin.castLE T.finrank_range_le ⟨k, hk⟩)) = 0 := by
    rw [prefix_sum]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hik : i.val < k
    · rw [ite_eq_left hik]
      have hne : Fin.castLE T.finrank_range_le i ≠
          Fin.castLE T.finrank_range_le ⟨k, hk⟩ := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_castLE] at hv
        omega
      have hinner : D05.firstInner (F := F)
          (d.domainBasis (Fin.castLE T.finrank_range_le ⟨k, hk⟩))
          (d.domainBasis (Fin.castLE T.finrank_range_le i)) = 0 := by
        rw [D05.firstInner, orthonormal_iff_ite.mp d.domainBasis.orthonormal,
          ite_eq_right hne]
      rw [hinner, mul_zero, zero_smul]
    · simp [hik]
  change ‖T _ - D05.svdTruncation T d k _‖ = _
  rw [hz, sub_zero, d.positive_action ⟨k, hk⟩, norm_smul,
    d.codomainBasis.orthonormal.norm_eq_one, mul_one, RCLike.norm_ofReal,
    abs_of_nonneg (T.singularValues_nonneg k)]

theorem error_norm : Specs.D05.M14.LowRank.Truncation.error_norm := by
  intro F V W _ _ _ _ _ _ _ T d k
  apply le_antisymm
  · rw [OperatorNorm.eq_continuous_opNorm]
    apply ContinuousLinearMap.opNorm_le_bound _ (T.singularValues_nonneg k)
    exact residual_norm_le T d k
  · by_cases hk : k < Module.finrank F T.range
    · obtain ⟨he, herr⟩ := residual_attains T d k hk
      have h := OperatorNorm.apply_le (T - D05.svdTruncation T d k)
        (d.domainBasis (Fin.castLE T.finrank_range_le ⟨k, hk⟩))
      rw [he, mul_one, herr] at h
      exact h
    · rw [T.singularValues_eq_zero_iff_le_finrank_range.mpr (Nat.le_of_not_gt hk)]
      exact OperatorNorm.nonneg _

theorem error_of_lt_rank : Specs.D05.M14.LowRank.Truncation.error_of_lt_rank := by
  intro F V W _ _ _ _ _ _ _ T d k hk
  exact error_norm T d k

theorem error_of_rank_le : Specs.D05.M14.LowRank.Truncation.error_of_rank_le := by
  intro F V W _ _ _ _ _ _ _ T d k hk
  exact ⟨eq_self_of_rank_le T d k hk, by
    rw [error_norm, T.singularValues_eq_zero_iff_le_finrank_range.mpr hk]⟩

theorem zero_truncation : Specs.D05.M14.LowRank.Truncation.zero_truncation := by
  intro F V W _ _ _ _ _ _ _ T d
  ext v
  simp [D05.svdTruncation]

theorem rank_zero : Specs.D05.M14.LowRank.Truncation.rank_zero := by
  intro F V W _ _ _ _ _ _ _ T d hr k
  exact error_of_rank_le T d k (by omega)

theorem zero_domain : Specs.D05.M14.LowRank.Truncation.zero_domain := by
  intro F V W _ _ _ _ _ _ _ T d hV k
  apply error_of_rank_le
  have h := T.finrank_range_le
  omega

theorem zero_codomain : Specs.D05.M14.LowRank.Truncation.zero_codomain := by
  intro F V W _ _ _ _ _ _ _ T d hW k
  apply error_of_rank_le
  have h := Submodule.finrank_le T.range
  omega

end D05.M14.LowRank.Truncation
