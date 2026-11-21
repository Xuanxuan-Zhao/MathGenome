import MathGenome.Internal.Specs.D05.M13.NormalBasic.NormKernel
import MathGenome.Internal.D05.M13.Normal
import MathGenome.Internal.D05.M13.SelfAdjoint.DiagonalTests
import MathGenome.Internal.D05.M13.AdjointKernel
import MathGenome.Internal.D05.M12.OrthogonalDecomposition

/-! Elementary normal-operator identities, without a spectral theorem. -/

namespace D05.M13.NormalBasic.NormKernel

/-- Adjoint reversal and involutivity fix both terms separately. -/
theorem commutator_selfAdjoint :
    Specs.D05.M13.NormalBasic.NormKernel.commutator_selfAdjoint := by
  intro F V _ _ _ _ T
  unfold D05.selfAdjoint
  simp only [map_sub, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]

/-- Move the adjoint across the inner product in each of the two terms. -/
theorem commutator_diagonal :
    Specs.D05.M13.NormalBasic.NormKernel.commutator_diagonal := by
  intro F V _ _ _ _ T x
  simp only [D05.firstInner, LinearMap.sub_apply, LinearMap.comp_apply, inner_sub_right]
  have h₁ := LinearMap.adjoint_inner_right T x (T x)
  have h₂ := LinearMap.adjoint_inner_right (LinearMap.adjoint T) x (LinearMap.adjoint T x)
  rw [LinearMap.adjoint_adjoint] at h₂
  rw [h₁, h₂, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]

/-- The reverse implication applies the upstream self-adjoint diagonal test to
T†T − TT†, rather than using any spectral decomposition. -/
theorem normal_iff_norm_adjoint :
    Specs.D05.M13.NormalBasic.NormKernel.normal_iff_norm_adjoint := by
  intro F V _ _ _ _ T
  constructor
  · intro hT x
    have hz : (LinearMap.adjoint T).comp T - T.comp (LinearMap.adjoint T) = 0 :=
      sub_eq_zero.mpr hT.symm
    have hd := commutator_diagonal T x
    rw [hz, LinearMap.zero_apply] at hd
    simp only [D05.firstInner, inner_zero_right] at hd
    have hs : ‖T x‖ ^ 2 = ‖LinearMap.adjoint T x‖ ^ 2 := by
      exact_mod_cast (sub_eq_zero.mp hd.symm)
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs
  · intro hn
    have hz := D05.M13.SelfAdjoint.DiagonalTests.selfAdjoint_zero_of_diagonal_zero
      ((LinearMap.adjoint T).comp T - T.comp (LinearMap.adjoint T))
      (commutator_selfAdjoint T) (fun x => by
        rw [commutator_diagonal, hn x, sub_self])
    exact (sub_eq_zero.mp hz).symm

theorem ker_eq_ker_adjoint :
    Specs.D05.M13.NormalBasic.NormKernel.ker_eq_ker_adjoint := by
  intro F V _ _ _ _ T hT
  ext x
  change T x = 0 ↔ LinearMap.adjoint T x = 0
  have hn := (normal_iff_norm_adjoint T).mp hT x
  constructor
  · intro hx
    apply norm_eq_zero.mp
    rw [← hn, hx, norm_zero]
  · intro hx
    apply norm_eq_zero.mp
    rw [hn, hx, norm_zero]

/-- Apply the general adjoint image formula to T† and then identify kernels. -/
theorem range_eq_orthogonal_ker :
    Specs.D05.M13.NormalBasic.NormKernel.range_eq_orthogonal_ker := by
  intro F V _ _ _ _ T hT
  have h := D05.M13.AdjointKernel.range_adjoint (LinearMap.adjoint T)
  rw [LinearMap.adjoint_adjoint, ← ker_eq_ker_adjoint T hT] at h
  exact h

theorem range_eq_range_adjoint :
    Specs.D05.M13.NormalBasic.NormKernel.range_eq_range_adjoint := by
  intro F V _ _ _ _ T hT
  exact (range_eq_orthogonal_ker T hT).trans
    (D05.M13.AdjointKernel.range_adjoint T).symm

/-- Transfer the already-proved orthogonal decomposition along ker T. -/
theorem orthogonal_direct_sum :
    Specs.D05.M13.NormalBasic.NormKernel.orthogonal_direct_sum := by
  intro F V _ _ _ _ T hT
  rw [range_eq_orthogonal_ker T hT]
  refine ⟨D05.M12.OrthogonalDecomposition.internal_direct_sum (LinearMap.ker T), ?_⟩
  intro x hx y hy
  exact inner_eq_zero_symm.mpr ((Submodule.mem_orthogonal _ _).mp hy x hx)

theorem exists_unique_components :
    Specs.D05.M13.NormalBasic.NormKernel.exists_unique_components := by
  intro F V _ _ _ _ T hT x
  rw [range_eq_orthogonal_ker T hT]
  exact D05.M12.OrthogonalDecomposition.exists_unique_components (LinearMap.ker T) x

end D05.M13.NormalBasic.NormKernel
