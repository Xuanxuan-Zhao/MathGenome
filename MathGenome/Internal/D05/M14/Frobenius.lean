import MathGenome.Internal.Specs.D05.M14.Frobenius
import MathGenome.Internal.D05.M04.Trace
import MathGenome.Internal.D05.M14.OperatorNorm

noncomputable section
namespace D05.M14.Frobenius

abbrev frobeniusNorm : Specs.D05.M14.Frobenius.frobeniusNorm_type :=
  fun T => D05.frobeniusNorm T

theorem nonneg : Specs.D05.M14.Frobenius.nonneg := by
  intro F V W _ _ _ _ _ _ _ T
  exact Real.sqrt_nonneg _

theorem column_trace : Specs.D05.M14.Frobenius.column_trace := by
  intro F V W _ _ _ _ _ _ _ I _ T e
  classical
  rw [LinearMap.trace_eq_matrix_trace F e.toBasis]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, LinearMap.comp_apply,
    LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K,
    RCLike.ofReal_sum, RCLike.ofReal_pow]

theorem squared_basis_sum : Specs.D05.M14.Frobenius.squared_basis_sum := by
  intro F V W _ _ _ _ _ _ _ I _ T e
  rw [D05.frobeniusNorm, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  apply RCLike.ofReal_injective (K := F)
  exact (column_trace T (stdOrthonormalBasis F V)).symm.trans (column_trace T e)

theorem trace_identity : Specs.D05.M14.Frobenius.trace_identity := by
  intro F V W _ _ _ _ _ _ _ T
  rw [squared_basis_sum T (stdOrthonormalBasis F V)]
  exact (column_trace T _).symm

theorem matrix_formula : Specs.D05.M14.Frobenius.matrix_formula := by
  intro F V W _ _ _ _ _ _ _ T I J _ _ e f
  classical
  rw [squared_basis_sum T e, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply] using
    (f.sum_sq_norm_inner_right (T (e j))).symm

theorem basis_independent : Specs.D05.M14.Frobenius.basis_independent := by
  intro F V W _ _ _ _ _ _ _ T I J _ _ e f I' J' _ _ e' f'
  exact (matrix_formula T e f).symm.trans (matrix_formula T e' f')

theorem eq_matrix_sqrt : Specs.D05.M14.Frobenius.eq_matrix_sqrt := by
  intro F V W _ _ _ _ _ _ _ T I J _ _ e f
  rw [← matrix_formula T e f, Real.sqrt_sq (nonneg T)]

/-- The positive block contributes sᵢ²; the kernel block contributes zero.
The injection into the full domain index set also works when rank is zero. -/
theorem singular_sum : Specs.D05.M14.Frobenius.singular_sum := by
  intro F V W _ _ _ _ _ _ _ T
  classical
  obtain ⟨d⟩ := D05.M14.Svd.exists_svd T
  rw [squared_basis_sum T d.domainBasis]
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
    rw [d.zero_action j hjr, norm_zero, zero_pow (by decide)]
  · intro i hi
    rw [d.positive_action, norm_smul, d.codomainBasis.orthonormal.norm_eq_one,
      mul_one, RCLike.norm_ofReal, abs_of_nonneg (T.singularValues_nonneg i)]

theorem positive_list_sum : Specs.D05.M14.Frobenius.positive_list_sum := by
  intro F V W _ _ _ _ _ _ _ T
  rw [singular_sum]
  simp [D05.positiveSingularValues, List.map_ofFn, List.sum_ofFn]

theorem zero_map : Specs.D05.M14.Frobenius.zero_map := by
  intro F V W _ _ _ _ _ _ _
  simp [D05.frobeniusNorm]

theorem rank_zero : Specs.D05.M14.Frobenius.rank_zero := by
  intro F V W _ _ _ _ _ _ _ T hr
  have hT : T = 0 := by
    rwa [← LinearMap.range_eq_bot, ← Submodule.finrank_eq_zero]
  subst T
  exact ⟨D05.M14.OperatorNorm.zero_map, zero_map⟩

theorem operator_le : Specs.D05.M14.Frobenius.operator_le := by
  intro F V W _ _ _ _ _ _ _ T
  classical
  by_cases hr : Module.finrank F (LinearMap.range T) = 0
  · rw [(rank_zero T hr).1, (rank_zero T hr).2]
  · have hp : 0 < Module.finrank F (LinearMap.range T) := Nat.pos_of_ne_zero hr
    apply (sq_le_sq₀ (D05.M14.OperatorNorm.nonneg T) (nonneg T)).mp
    rw [D05.M14.OperatorNorm.eq_first_singularValue, singular_sum]
    exact Finset.single_le_sum
      (fun (i : Fin (Module.finrank F (LinearMap.range T))) hi =>
        sq_nonneg (T.singularValues i))
      (Finset.mem_univ (⟨0, hp⟩ : Fin (Module.finrank F (LinearMap.range T))))

theorem le_sqrt_rank_mul_operator : Specs.D05.M14.Frobenius.le_sqrt_rank_mul_operator := by
  intro F V W _ _ _ _ _ _ _ T
  classical
  apply (sq_le_sq₀ (nonneg T)
    (mul_nonneg (Real.sqrt_nonneg _) (D05.M14.OperatorNorm.nonneg T))).mp
  rw [singular_sum, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _),
    D05.M14.OperatorNorm.eq_first_singularValue]
  calc
    (∑ i : Fin (Module.finrank F (LinearMap.range T)), T.singularValues i ^ 2) ≤
        ∑ _i : Fin (Module.finrank F (LinearMap.range T)), T.singularValues 0 ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact (sq_le_sq₀ (T.singularValues_nonneg i) (T.singularValues_nonneg 0)).mpr
        (T.singularValues_antitone (Nat.zero_le _))
    _ = _ := by simp

end D05.M14.Frobenius
