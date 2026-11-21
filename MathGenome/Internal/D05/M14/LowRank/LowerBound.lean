import MathGenome.Internal.Specs.D05.M14.LowRank.LowerBound
import MathGenome.Internal.D05.M14.Svd
import MathGenome.Internal.D05.M14.OperatorNorm
import MathGenome.Internal.D05.M03.RankNullity
import MathGenome.Internal.D05.M12.FourierParseval
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section
namespace D05.M14.LowRank.LowerBound
open scoped BigOperators

theorem span_norm_lower : Specs.D05.M14.LowRank.LowerBound.span_norm_lower := by
  intro F V W _ _ _ _ _ _ _ T d k hk x hx
  classical
  let jrank : Fin (k + 1) → Fin (Module.finrank F T.range) :=
    Fin.castLE (Nat.succ_le_of_lt hk)
  let e : Fin (k + 1) → V := fun j =>
    d.domainBasis (Fin.castLE T.finrank_range_le (jrank j))
  let f : Fin (k + 1) → W := fun j =>
    d.codomainBasis (Fin.castLE (Submodule.finrank_le _) (jrank j))
  have he : D05.orthonormalFamily (F := F) e :=
    (D05.M12.Orthonormal.orthonormal_iff_mathlib e).mpr
      ((d.domainBasis.orthonormal.comp _ (Fin.castLE_injective _)).comp _
        (Fin.castLE_injective _))
  have hf : D05.orthonormalFamily (F := F) f :=
    (D05.M12.Orthonormal.orthonormal_iff_mathlib f).mpr
      ((d.codomainBasis.orthonormal.comp _ (Fin.castLE_injective _)).comp _
        (Fin.castLE_injective _))
  change x ∈ Submodule.span F (Set.range e) at hx
  rw [← Fintype.range_linearCombination] at hx
  obtain ⟨a, rfl⟩ := hx
  change T.singularValues k * ‖∑ j, a j • e j‖ ≤ ‖T (∑ j, a j • e j)‖
  have hnorm := D05.M12.FourierParseval.norm_sq_finite_sum e he Finset.univ a
  have hT : T (∑ j, a j • e j) =
      ∑ j, (a j * (T.singularValues j : F)) • f j := by
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show T (e j) = (T.singularValues j : F) • f j from d.positive_action (jrank j),
      smul_smul]
  have hnormT : ‖T (∑ j, a j • e j)‖ ^ 2 =
      ∑ j : Fin (k + 1), ‖a j‖ ^ 2 * T.singularValues j ^ 2 := by
    rw [hT, D05.M12.FourierParseval.norm_sq_finite_sum f hf Finset.univ]
    apply Finset.sum_congr rfl
    intro j hj
    rw [norm_mul, RCLike.norm_ofReal,
      abs_of_nonneg (T.singularValues_nonneg j), mul_pow]
  apply (sq_le_sq₀ (mul_nonneg (T.singularValues_nonneg k) (norm_nonneg _))
    (norm_nonneg _)).mp
  rw [mul_pow, hnorm, hnormT, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [mul_comm (T.singularValues k ^ 2)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact (sq_le_sq₀ (T.singularValues_nonneg k) (T.singularValues_nonneg j)).mpr
    (T.singularValues_antitone (Nat.le_of_lt_succ j.isLt))

/-- Rank-nullity for restriction to a subspace, followed by normalization. -/
private theorem unit_in_subspace_kernel
    {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (S : V →ₗ[F] W) (E : Submodule F V)
    (h : Module.finrank F S.range < Module.finrank F E) :
    ∃ x : V, x ∈ E ∧ S x = 0 ∧ ‖x‖ = 1 := by
  let R := S.comp E.subtype
  have hR : Module.finrank F R.range ≤ Module.finrank F S.range :=
    Submodule.finrank_mono (LinearMap.range_comp_le_range E.subtype S)
  have hrn := R.finrank_range_add_finrank_ker
  have hker : 0 < Module.finrank F R.ker := by omega
  obtain ⟨y, hy⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := F) (M := R.ker)).mp hker
  let x : V := y.val.val
  have hx : x ≠ 0 := by
    intro h
    apply hy
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hxE : x ∈ E := y.val.property
  have hxS : S x = 0 := y.property
  let z : V := ((‖x‖⁻¹ : ℝ) : F) • x
  have hzE : z ∈ E := E.smul_mem _ hxE
  have hzS : S z = 0 := by simp [z, hxS]
  have hz : ‖z‖ = 1 := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  exact ⟨z, hzE, hzS, hz⟩

theorem unit_kernel_vector : Specs.D05.M14.LowRank.LowerBound.unit_kernel_vector := by
  intro F V W _ _ _ _ _ _ _ T S d k hk hS
  classical
  let e : Fin (k + 1) → V := fun j =>
    d.domainBasis (Fin.castLE T.finrank_range_le (Fin.castLE (Nat.succ_le_of_lt hk) j))
  let E := Submodule.span F (Set.range e)
  have he : Orthonormal F e :=
    (d.domainBasis.orthonormal.comp _ (Fin.castLE_injective _)).comp _
      (Fin.castLE_injective _)
  have hE : Module.finrank F E = k + 1 := by
    simpa using finrank_span_eq_card he.linearIndependent
  obtain ⟨x, hxE, hxS, hx⟩ := unit_in_subspace_kernel S E (by omega)
  refine ⟨x, hxE, hxS, hx, ?_⟩
  simpa only [hx, mul_one] using span_norm_lower T d k hk x hxE

theorem lower_bound : Specs.D05.M14.LowRank.LowerBound.lower_bound := by
  intro F V W _ _ _ _ _ _ _ T S k hk hS
  obtain ⟨d⟩ := D05.M14.Svd.exists_svd T
  obtain ⟨x, _, hxS, hx, hTx⟩ := unit_kernel_vector T S d k hk hS
  have h := D05.M14.OperatorNorm.apply_le (T - S) x
  simp only [LinearMap.sub_apply, hxS, sub_zero, hx, mul_one] at h
  exact hTx.trans h

end D05.M14.LowRank.LowerBound
