import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.PreHilbertProjection
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.CompleteTargetProjection

/-!
Projection in possibly incomplete inner-product spaces. The accepted convex
projection theorem supplies the full complete-convex-set assertion. For a
linear target, Mathlib constructs the scalar-linear orthogonal projector from
completeness of that target alone. Its orthogonal residual supplies the unique
direct-sum coordinates, and its native operator norm is at most one.
-/

noncomputable section

namespace ExpandedFA.Hilbert.PreHilbertProjection
universe u v

theorem existsUnique_nearestPoint : Spec.ExistsUniqueNearestPoint.{u, v} :=
  CompleteTargetProjection.existsUnique_nearestPoint

theorem minimizer_iff_variational : Spec.MinimizerIffVariational.{u, v} :=
  CompleteTargetProjection.minimizer_iff_variational

theorem convexProjection_nonexpansive : Spec.ConvexProjectionNonexpansive.{u, v} :=
  CompleteTargetProjection.convexProjection_nonexpansive

theorem complete_subspace_decomposition : Spec.CompleteSubspaceDecomposition.{u, v} := by
  intro 𝕜 E _ _ _ Y hc
  let : CompleteSpace Y := hc.completeSpace_coe
  refine ⟨Y.isTopCompl_orthogonal, ?_⟩
  intro x
  refine ⟨(Y.orthogonalProjectionOnto x,
    ⟨x - Y.starProjection x, Y.sub_starProjection_mem_orthogonal x⟩), ?_, ?_⟩
  · exact add_sub_cancel _ _
  · rintro ⟨y, z⟩ hyz
    have hy : Y.starProjection x = (y : E) :=
      Submodule.eq_starProjection_of_mem_orthogonal' y.2 z.2 hyz.symm
    apply Prod.ext
    · exact Subtype.ext hy.symm
    · apply Subtype.ext
      change (z : E) = x - Y.starProjection x
      rw [hy, ← hyz]
      exact (add_sub_cancel_left _ _).symm

theorem complete_subspace_projection : Spec.CompleteSubspaceProjection.{u, v} := by
  intro 𝕜 E _ _ _ Y hc
  let : CompleteSpace Y := hc.completeSpace_coe
  change ‖Y.starProjection‖ ≤ 1 ∧ _
  refine ⟨Y.starProjection_norm_le, ?_, ?_, ?_, Y.lipschitzWith_starProjection⟩
  · intro x
    exact ⟨Y.starProjection_apply_mem x, Y.sub_starProjection_mem_orthogonal x⟩
  · intro y hy
    exact Y.starProjection_eq_self_iff.mpr hy
  · intro x z hz
    change ‖x - Y.starProjection x‖ ≤ ‖x - z‖
    rw [Y.starProjection_minimal x]
    exact ciInf_le (f := fun w : Y => ‖x - w‖)
      ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ ⟨z, hz⟩

theorem zero_subspace_projection : Spec.ZeroSubspaceProjection.{u, v} := by
  intro 𝕜 E _ _ _
  change (⊥ : Submodule 𝕜 E).starProjection = 0 ∧
    ‖(⊥ : Submodule 𝕜 E).starProjection‖ = 0
  simp only [Submodule.starProjection_bot, norm_zero, and_self]

end ExpandedFA.Hilbert.PreHilbertProjection
