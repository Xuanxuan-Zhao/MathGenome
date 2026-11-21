import MathGenome.Internal.Specs.D05.M14.Svd
import MathGenome.Internal.D05.M14.SingularValues
import MathGenome.Internal.D05.M14.Svd.PairedVectors
import MathGenome.Internal.D05.M12.OnBasis

noncomputable section

namespace D05.M14.Svd

open scoped BigOperators

/-- Select the ordered eigenbasis of T†T, normalize its positive images, and
extend those images while retaining every prescribed vector. -/
theorem exists_svd : Specs.D05.M14.Svd.exists_svd := by
  intro F V W _ _ _ _ _ _ _ T
  classical
  let e := T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
  let s : Fin (Module.finrank F V) → ℝ := fun i => T.singularValues i
  have he : ∀ i, (LinearMap.adjoint T) (T (e i)) = ((s i ^ 2 : ℝ) : F) • e i := by
    intro i
    dsimp only [e, s]
    rw [T.sq_singularValues_fin rfl i]
    exact T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i
  have hp : ∀ i : Fin (Module.finrank F (LinearMap.range T)),
      0 < s (Fin.castLE T.finrank_range_le i) := by
    intro i
    exact (SingularValues.positive_iff T i.val).mpr i.isLt
  have ho := PairedVectors.paired_orthonormal T e s he T.finrank_range_le hp
  obtain ⟨hm, b, hb, hbe⟩ := D05.M12.OnBasis.extend_orthonormal_list _ ho
  let f := b.toOrthonormalBasis
    ((D05.M12.Orthonormal.orthonormal_iff_mathlib _).mp hb)
  refine ⟨⟨e, f, ?_, ?_⟩⟩
  · intro i
    have hf : f (Fin.castLE (Submodule.finrank_le _) i) =
        (T.singularValues i : F)⁻¹ • T (e (Fin.castLE T.finrank_range_le i)) := by
      simpa only [f, Module.Basis.coe_toOrthonormalBasis, s, Fin.val_castLE] using hbe i
    rw [hf, smul_smul, mul_inv_cancel₀, one_smul]
    exact_mod_cast (ne_of_gt (hp i))
  · intro i hi
    exact PairedVectors.zero_image T e s he i ((SingularValues.zero_iff T i.val).mpr hi)

theorem expansion : Specs.D05.M14.Svd.expansion := by
  intro F V W _ _ _ _ _ _ _ T d v
  classical
  have h := congrArg T (d.domainBasis.sum_repr v)
  simp only [map_sum, map_smul, OrthonormalBasis.repr_apply_apply] at h
  rw [← h]
  symm
  apply Finset.sum_of_injOn (fun i => Fin.castLE T.finrank_range_le i)
  · intro i hi j hj hij
    exact Fin.ext (congrArg (fun x : Fin (Module.finrank F V) => x.val) hij)
  · intro i hi
    simp
  · intro j hj hnot
    have hjr : Module.finrank F (LinearMap.range T) ≤ j.val := by
      by_contra hn
      exact hnot ⟨⟨j.val, Nat.lt_of_not_ge hn⟩, Finset.mem_univ _, rfl⟩
    rw [d.zero_action j hjr, smul_zero]
  · intro i hi
    rw [d.positive_action, smul_smul]
    simp [D05.firstInner, mul_comm]

theorem rectangular_diagonal : Specs.D05.M14.Svd.rectangular_diagonal := by
  intro F V W _ _ _ _ _ _ _ T d i j
  classical
  rw [LinearMap.toMatrix_apply]
  by_cases hj : j.val < Module.finrank F (LinearMap.range T)
  · let k : Fin (Module.finrank F (LinearMap.range T)) := ⟨j.val, hj⟩
    have hjk : j = Fin.castLE T.finrank_range_le k := rfl
    rw [hjk, OrthonormalBasis.coe_toBasis, d.positive_action]
    simp [Fin.ext_iff, k, RCLike.real_smul_eq_coe_mul]
  · rw [OrthonormalBasis.coe_toBasis, d.zero_action j (Nat.le_of_not_lt hj)]
    simp [(SingularValues.zero_iff T j.val).mpr (Nat.le_of_not_lt hj)]

theorem diagonal_signs : Specs.D05.M14.Svd.diagonal_signs := by
  intro F V W _ _ _ _ _ _ _ T
  exact ⟨fun i => T.singularValues_nonneg i,
    fun i => (SingularValues.positive_iff T i.val).mpr i.isLt,
    fun i hi => (SingularValues.zero_iff T i.val).mpr hi⟩

theorem zero_map_bases : Specs.D05.M14.Svd.zero_map_bases := by
  intro F V W _ _ _ _ _ _ _ e f
  refine ⟨⟨e, f, ?_, ?_⟩, rfl, rfl⟩
  · intro i
    have hzero : Module.finrank F (LinearMap.range (0 : V →ₗ[F] W)) = 0 := by simp
    exact Fin.elim0 (Fin.cast hzero i)
  · intro i hi
    rfl

end D05.M14.Svd
