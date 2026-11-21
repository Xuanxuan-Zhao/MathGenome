import MathGenome.Internal.Specs.D05.M13.NormalBasic
import MathGenome.Internal.D05.M13.NormalBasic.NormKernel
import MathGenome.Internal.D05.M13.NormalBasic.ShiftEigenvectors
import Mathlib.Tactic.Module

/-! K05.13.normal_basic: elementary normal identities and complex parts.
No spectral theorem is used. -/

namespace D05.M13.NormalBasic

theorem normal_iff_norm_adjoint : Specs.D05.M13.NormalBasic.normal_iff_norm_adjoint :=
  NormKernel.normal_iff_norm_adjoint

theorem ker_eq_ker_adjoint : Specs.D05.M13.NormalBasic.ker_eq_ker_adjoint :=
  NormKernel.ker_eq_ker_adjoint

theorem range_eq_range_adjoint : Specs.D05.M13.NormalBasic.range_eq_range_adjoint :=
  NormKernel.range_eq_range_adjoint

theorem range_eq_orthogonal_ker : Specs.D05.M13.NormalBasic.range_eq_orthogonal_ker :=
  NormKernel.range_eq_orthogonal_ker

theorem orthogonal_direct_sum : Specs.D05.M13.NormalBasic.orthogonal_direct_sum :=
  NormKernel.orthogonal_direct_sum

theorem exists_unique_components : Specs.D05.M13.NormalBasic.exists_unique_components :=
  NormKernel.exists_unique_components

theorem adjoint_shift : Specs.D05.M13.NormalBasic.adjoint_shift :=
  ShiftEigenvectors.adjoint_shift

theorem shift_normal : Specs.D05.M13.NormalBasic.shift_normal :=
  ShiftEigenvectors.shift_normal

theorem eigenvector_equation_iff : Specs.D05.M13.NormalBasic.eigenvector_equation_iff :=
  ShiftEigenvectors.eigenvector_equation_iff

theorem eigenspace_adjoint : Specs.D05.M13.NormalBasic.eigenspace_adjoint :=
  ShiftEigenvectors.eigenspace_adjoint

theorem eigenvectors_orthogonal : Specs.D05.M13.NormalBasic.eigenvectors_orthogonal :=
  ShiftEigenvectors.eigenvectors_orthogonal

theorem eigenspaces_orthogonal : Specs.D05.M13.NormalBasic.eigenspaces_orthogonal :=
  ShiftEigenvectors.eigenspaces_orthogonal

/-- Conjugate the scalar division and exchange the two summands. -/
theorem real_part_selfAdjoint : Specs.D05.M13.NormalBasic.real_part_selfAdjoint := by
  intro V _ _ _ T
  unfold D05.selfAdjoint
  rw [D05.M13.AdjointLaws.adjoint_smul, D05.M13.AdjointLaws.adjoint_add,
    LinearMap.adjoint_adjoint]
  simp only [map_inv₀, map_ofNat]
  rw [add_comm T]

/-- Both the imaginary scalar and the difference change sign under adjoint. -/
theorem imag_part_selfAdjoint : Specs.D05.M13.NormalBasic.imag_part_selfAdjoint := by
  intro V _ _ _ T
  unfold D05.selfAdjoint
  rw [D05.M13.AdjointLaws.adjoint_smul, map_sub, LinearMap.adjoint_adjoint]
  simp only [map_inv₀, map_mul, map_ofNat, Complex.conj_I, mul_neg, inv_neg]
  module

/-- Ordinary scalar arithmetic reconstructs T from the two specified parts. -/
theorem complex_decomposition : Specs.D05.M13.NormalBasic.complex_decomposition := by
  intro V _ _ _ T
  have hi : Complex.I * (2 * Complex.I)⁻¹ = (2 : ℂ)⁻¹ := by
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ Complex.I_ne_zero, one_mul]
  rw [smul_smul, hi]
  module

/-- Expanding four compositions cancels the two pure-square terms. -/
theorem parts_commutator : Specs.D05.M13.NormalBasic.parts_commutator := by
  intro V _ _ _ T
  dsimp only
  ext x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_smul, map_add, map_sub]
  match_scalars <;> ring

/-- The scalar 1/(2i) is nonzero, so the commutator vanishes exactly when
TT† = T†T. -/
theorem normal_iff_parts_commute : Specs.D05.M13.NormalBasic.normal_iff_parts_commute := by
  intro V _ _ _ T
  dsimp only
  rw [← sub_eq_zero, parts_commutator]
  rw [smul_eq_zero]
  have hc : (2 * Complex.I)⁻¹ ≠ (0 : ℂ) := inv_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  simp only [hc, false_or, sub_eq_zero]
  exact eq_comm

/-- Adding and subtracting the adjoint identity forces the real and imaginary
parts in every self-adjoint expression T = A + iB. -/
theorem complex_parts_unique : Specs.D05.M13.NormalBasic.complex_parts_unique := by
  intro V _ _ _ T A B hA hB hT
  have hadj : LinearMap.adjoint T = A - Complex.I • B := by
    rw [hT, D05.M13.AdjointLaws.adjoint_add, D05.M13.AdjointLaws.adjoint_smul,
      ← hA, ← hB]
    simp [sub_eq_add_neg]
  rw [hadj, hT]
  constructor
  · module
  · match_scalars <;> ring_nf
    simp

end D05.M13.NormalBasic
