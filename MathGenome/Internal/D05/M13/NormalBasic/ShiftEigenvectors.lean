import MathGenome.Internal.Specs.D05.M13.NormalBasic.ShiftEigenvectors
import MathGenome.Internal.D05.M13.NormalBasic.NormKernel
import MathGenome.Internal.D05.M13.AdjointLaws
import MathGenome.Internal.D05.M09.Eigenspace

/-! Scalar shifts and orthogonality for normal maps, before any eigenbasis choice. -/

namespace D05.M13.NormalBasic.ShiftEigenvectors

theorem adjoint_shift :
    Specs.D05.M13.NormalBasic.ShiftEigenvectors.adjoint_shift := by
  intro F V _ _ _ _ T μ
  rw [map_sub, D05.M13.AdjointLaws.adjoint_smul, D05.M13.AdjointLaws.adjoint_id]

/-- Expand the products and cancel the scalar cross terms. -/
theorem shift_normal :
    Specs.D05.M13.NormalBasic.ShiftEigenvectors.shift_normal := by
  intro F V _ _ _ _ T hT μ
  unfold D05.normalOperator at *
  rw [adjoint_shift]
  ext x
  have hx := DFunLike.congr_fun hT x
  simp only [LinearMap.comp_apply] at hx
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_sub, map_smul, smul_sub, smul_smul]
  rw [hx, mul_comm μ (starRingEnd F μ)]
  abel

/-- Apply equality of kernels to the shifted map; neither direction requires
the vector to be nonzero. -/
theorem eigenvector_equation_iff :
    Specs.D05.M13.NormalBasic.ShiftEigenvectors.eigenvector_equation_iff := by
  intro F V _ _ _ _ T hT μ x
  have hk := D05.M13.NormalBasic.NormKernel.ker_eq_ker_adjoint
    (T - μ • LinearMap.id) (shift_normal T hT μ)
  have hm : x ∈ LinearMap.ker (T - μ • LinearMap.id) ↔
      x ∈ LinearMap.ker (LinearMap.adjoint (T - μ • LinearMap.id)) := by
    rw [hk]
  rw [adjoint_shift] at hm
  simpa only [LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] using hm

theorem eigenspace_adjoint :
    Specs.D05.M13.NormalBasic.ShiftEigenvectors.eigenspace_adjoint := by
  intro F V _ _ _ _ T hT μ
  ext x
  rw [D05.M09.Eigenspace.mem_eigenspace_iff,
    D05.M09.Eigenspace.mem_eigenspace_iff]
  exact eigenvector_equation_iff T hT μ x

/-- The adjoint identity makes α h(x,y) = β h(x,y). Cancel α − β. -/
theorem eigenvectors_orthogonal :
    Specs.D05.M13.NormalBasic.ShiftEigenvectors.eigenvectors_orthogonal := by
  intro F V _ _ _ _ T hT α β hαβ x y hx hy
  have hy' := (eigenvector_equation_iff T hT β y).mp hy
  have he := D05.M13.Adjoint.adjoint_identity T x y
  rw [hx, hy'] at he
  simp only [D05.firstInner, inner_smul_right, inner_smul_left,
    starRingEnd_self_apply] at he
  have hz : (α - β) * D05.firstInner (F := F) x y = 0 := by
    rw [sub_mul, sub_eq_zero]
    exact he
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hαβ)

theorem eigenspaces_orthogonal :
    Specs.D05.M13.NormalBasic.ShiftEigenvectors.eigenspaces_orthogonal := by
  intro F V _ _ _ _ T hT α β hαβ x hx
  apply (Submodule.mem_orthogonal _ x).mpr
  intro y hy
  exact eigenvectors_orthogonal T hT α β hαβ x y
    ((D05.M09.Eigenspace.mem_eigenspace_iff T α x).mp hx)
    ((D05.M09.Eigenspace.mem_eigenspace_iff T β y).mp hy)

end D05.M13.NormalBasic.ShiftEigenvectors
