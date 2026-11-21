import MathGenome.Internal.Specs.D05.M12.Orthonormal
import MathGenome.Internal.D05.M02.Independence
import MathGenome.Internal.D05.M12.Norm

/-! K05.12.orthonormal: indexed orthogonal families and normalization. -/

noncomputable section

namespace D05.M12.Orthonormal

abbrev orthonormal : Specs.D05.M12.Orthonormal.orthonormal_type :=
  @_root_.D05.orthonormalFamily

abbrev orthogonal : Specs.D05.M12.Orthonormal.orthogonal_type :=
  @_root_.D05.orthogonalFamily

abbrev normalizeVector : Specs.D05.M12.Orthonormal.normalizeVector_type :=
  @_root_.D05.normalizeVector

theorem orthonormal_iff_mathlib : Specs.D05.M12.Orthonormal.orthonormal_iff_mathlib := by
  intro F V J _ _ _ e
  classical
  rw [orthonormal_iff_ite]
  constructor <;> intro h j k
  · simpa only [D05.firstInner, eq_comm] using h k j
  · simpa only [D05.firstInner, eq_comm] using h k j

theorem orthogonal_iff_pairwise : Specs.D05.M12.Orthonormal.orthogonal_iff_pairwise := by
  intro F V J _ _ _ e
  constructor <;> intro h j k hjk
  · exact h k j hjk.symm
  · exact h hjk.symm

theorem orthonormal_iff_orthogonal_norm_one :
    Specs.D05.M12.Orthonormal.orthonormal_iff_orthogonal_norm_one := by
  intro F V J _ _ _ e
  rw [orthonormal_iff_mathlib, orthogonal_iff_pairwise]
  exact and_comm

theorem orthonormal_linearIndependent :
    Specs.D05.M12.Orthonormal.orthonormal_linearIndependent := by
  intro F V J _ _ _ e he
  exact (orthonormal_iff_mathlib e |>.mp he).linearIndependent

theorem coefficient_finite_sum : Specs.D05.M12.Orthonormal.coefficient_finite_sum := by
  intro F V J _ _ _ e he s a k hk
  exact (orthonormal_iff_mathlib e |>.mp he).inner_right_sum a hk

theorem orthonormal_ne_zero : Specs.D05.M12.Orthonormal.orthonormal_ne_zero := by
  intro F V J _ _ _ e he j
  exact (orthonormal_linearIndependent e he).ne_zero j

theorem normalization_denominator_pos :
    Specs.D05.M12.Orthonormal.normalization_denominator_pos := by
  intro F V _ _ _ v hv
  exact norm_pos_iff.mpr hv

theorem normalizeVector_eq_inducedNorm :
    Specs.D05.M12.Orthonormal.normalizeVector_eq_inducedNorm := by
  intro F V _ _ _ v
  rw [D05.M12.Norm.inducedNorm_eq_norm]
  rfl

theorem normalizeVector_norm : Specs.D05.M12.Orthonormal.normalizeVector_norm := by
  intro F V _ _ _ v hv
  simp only [D05.normalizeVector, norm_smul, RCLike.norm_ofReal,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)

/-- Normalizing changes only scalar factors, so off-diagonal inner products
remain zero. The separate norm calculation supplies the diagonal ones. -/
theorem normalize_orthogonal : Specs.D05.M12.Orthonormal.normalize_orthogonal := by
  intro F V J _ _ _ e he hne
  apply (orthonormal_iff_orthogonal_norm_one _).mpr
  refine ⟨?_, fun j => normalizeVector_norm (e j) (hne j)⟩
  intro j k hjk
  change inner F _ _ = 0
  simp only [D05.normalizeVector, inner_smul_left, inner_smul_right]
  have hz : inner F (e k) (e j) = 0 := he j k hjk
  rw [hz, mul_zero, mul_zero]

theorem normalize_finite_orthogonal :
    Specs.D05.M12.Orthonormal.normalize_finite_orthogonal := by
  intro F V J _ _ _ _ e he hne
  exact normalize_orthogonal e he hne

theorem normalizeVector_zero : Specs.D05.M12.Orthonormal.normalizeVector_zero := by
  intro F V _ _ _
  simp [D05.normalizeVector]

theorem not_independent_of_zero_entry :
    Specs.D05.M12.Orthonormal.not_independent_of_zero_entry := by
  intro F V J _ _ _ e j hj
  exact D05.M02.Independence.not_independent_of_zero_entry e j hj

end D05.M12.Orthonormal
