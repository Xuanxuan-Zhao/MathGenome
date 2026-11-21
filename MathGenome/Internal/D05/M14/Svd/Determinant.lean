import MathGenome.Internal.Specs.D05.M14.Svd.Determinant
import MathGenome.Internal.D05.M14.SingularValues
import MathGenome.Internal.D05.M05.DetProduct
import MathGenome.Internal.D05.M13.AdjointLaws
import Mathlib.Analysis.InnerProductSpace.NormDet

/-! Determinant and the full finite list of singular values.
The library norm determinant is used only through its proved identities with
endomorphism determinants, Gram determinants, and the first dim(V) singular
values. The source-list bridge retains all zero occurrences.
-/

noncomputable section

namespace D05.M14.Svd.Determinant

theorem det_adjoint : Specs.D05.M14.Svd.Determinant.det_adjoint := by
  intro F V _ _ _ _ T
  let b := stdOrthonormalBasis F V
  rw [← LinearMap.det_toMatrix b.toBasis, LinearMap.toMatrix_adjoint,
    Matrix.det_conjTranspose, LinearMap.det_toMatrix]
  simp only [starRingEnd_apply]

theorem det_gram : Specs.D05.M14.Svd.Determinant.det_gram := by
  intro F V _ _ _ _ T
  rw [← T.normDet_sq, T.normDet_eq_norm_det]

theorem gram_det_real_nonneg : Specs.D05.M14.Svd.Determinant.gram_det_real_nonneg := by
  intro F V _ _ _ _ T
  rw [det_gram, RCLike.ofReal_re]
  exact ⟨rfl, sq_nonneg _⟩

theorem norm_det_eq_sqrt : Specs.D05.M14.Svd.Determinant.norm_det_eq_sqrt := by
  intro F V _ _ _ _ T
  rw [det_gram, RCLike.ofReal_re, Real.sqrt_sq (norm_nonneg _)]

theorem norm_det_eq_prod : Specs.D05.M14.Svd.Determinant.norm_det_eq_prod := by
  intro F V _ _ _ _ T
  rw [D05.M14.SingularValues.library_prefix T, Fin.prod_ofFn,
    Fin.prod_univ_eq_prod_range, ← T.normDet_eq_prod_singularValues,
    T.normDet_eq_norm_det]

theorem determinant_identity : Specs.D05.M14.Svd.Determinant.determinant_identity := by
  intro F V _ _ _ _ T
  exact ⟨norm_det_eq_sqrt T, (norm_det_eq_sqrt T).symm.trans (norm_det_eq_prod T)⟩

theorem singular_case : Specs.D05.M14.Svd.Determinant.singular_case := by
  intro F V _ _ _ _ T hT
  have hk : LinearMap.ker T ≠ ⊥ := fun h => hT (LinearMap.ker_eq_bot.mp h)
  have hd : T.det = 0 := LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk
  have hp : (D05.singularValues T).prod = 0 := by
    rw [← norm_det_eq_prod T, hd, norm_zero]
  refine ⟨List.prod_eq_zero_iff.mp hp, hd, ?_, hp⟩
  rw [← norm_det_eq_sqrt T, hd, norm_zero]

theorem zero_dim_case : Specs.D05.M14.Svd.Determinant.zero_dim_case := by
  intro F V _ _ _ _ T hn
  have hd := LinearMap.det_eq_one_of_finrank_eq_zero hn T
  have hl := (D05.M14.SingularValues.empty_domain T hn).1
  refine ⟨hd, hl, ?_, by rw [hl]; rfl⟩
  rw [← norm_det_eq_sqrt T, hd, norm_one]

theorem coordinate_determinant : Specs.D05.M14.Svd.Determinant.coordinate_determinant := by
  intro F V _ _ _ _ T n b
  rw [D05.M05.DetDefinition.matrix_det_bridge, LinearMap.det_toMatrix]
  exact norm_det_eq_prod T

theorem positive_only_not_eq : Specs.D05.M14.Svd.Determinant.positive_only_not_eq := by
  intro F V _ _ _ _ T hT
  have hp : 0 < (D05.positiveSingularValues T).prod :=
    List.prod_pos (D05.M14.SingularValues.positive_entries T)
  rw [(singular_case T hT).2.1, norm_zero]
  exact ne_of_gt hp

end D05.M14.Svd.Determinant
