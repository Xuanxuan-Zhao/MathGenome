import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Projection
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.PreHilbertProjection

/-!
The closed convex projection theorem (`paper.tex` 7372–7382).
Closedness in H gives exactly the target completeness needed by the accepted
pre-Hilbert projection theorem. The shared native orthogonal projector agrees
with the convex nearest-point projector by uniqueness. Its inner-product
identity gives self-adjointness. For arbitrary L, Mathlib's double-orthogonal
identity uses projection onto the closed subspace closure L; it imposes no
closedness assumption on L itself.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExpandedFA.Hilbert.Projection
universe u v

/-- Nearest-point projection onto a nonempty closed real-convex subset of H. -/
def convexProjection : Spec.ConvexProjectionType.{u, v} := Spec.ConvexProjectionValue

theorem existsUnique_nearestPoint : Spec.ExistsUniqueNearestPoint.{u, v} := by
  intro 𝕜 H _ _ _ _ C hne hclosed hv x
  exact PreHilbertProjection.existsUnique_nearestPoint 𝕜 H C hne hclosed.isComplete hv x

theorem minimizer_iff_variational : Spec.MinimizerIffVariational.{u, v} :=
  PreHilbertProjection.minimizer_iff_variational

theorem convexProjection_spec : Spec.ConvexProjectionSpec.{u, v} := by
  intro 𝕜 H _ _ _ _ C hne hclosed hv x
  exact CompleteTargetProjection.convexProjection_spec 𝕜 H C hne hclosed.isComplete hv x

theorem eq_convexProjection_iff_variational :
    Spec.EqConvexProjectionIffVariational.{u, v} := by
  intro 𝕜 H _ _ _ _ C hne hclosed hv x p
  exact CompleteTargetProjection.eq_convexProjection_iff_variational
    𝕜 H C hne hclosed.isComplete hv x p

theorem convexProjection_nonexpansive : Spec.ConvexProjectionNonexpansive.{u, v} := by
  intro 𝕜 H _ _ _ _ C hne hclosed hv x y
  exact PreHilbertProjection.convexProjection_nonexpansive
    𝕜 H C hne hclosed.isComplete hv x y

theorem closed_subspace_decomposition : Spec.ClosedSubspaceDecomposition.{u, v} := by
  intro 𝕜 H _ _ _ _ M hM
  exact PreHilbertProjection.complete_subspace_decomposition 𝕜 H M hM.isComplete

theorem closed_subspace_projection : Spec.ClosedSubspaceProjection.{u, v} := by
  intro 𝕜 H _ _ _ _ M hM
  let : CompleteSpace M := hM.completeSpace_coe
  change (∀ (c : 𝕜) (x y : H), M.starProjection (c • x + y) =
    c • M.starProjection x + M.starProjection y) ∧ _
  refine ⟨?_, isSelfAdjoint_starProjection M,
    M.inner_starProjection_left_eq_right, M.starProjection_norm_le, ?_, ?_, ?_⟩
  · intro c x y
    rw [map_add, map_smul]
  · intro x
    exact M.norm_starProjection_apply_le x
  · intro x
    exact ⟨M.starProjection_apply_mem x, M.sub_starProjection_mem_orthogonal x⟩
  · ext x
    exact M.starProjection_eq_self_iff.mpr (M.starProjection_apply_mem x)

theorem orthogonalProjection_eq_convexProjection :
    Spec.OrthogonalProjectionEqConvexProjection.{u, v} := by
  intro 𝕜 H _ _ _ _ M hM
  let : CompleteSpace M := hM.completeSpace_coe
  let := Conventions.realification 𝕜 H
  intro x
  apply (eq_convexProjection_iff_variational 𝕜 H (M : Set H)
    ⟨0, M.zero_mem⟩ hM (M.restrictScalars ℝ).convex x (M.starProjection x)).mpr
  refine ⟨M.starProjection_apply_mem x, ?_⟩
  intro z hz
  rw [Submodule.starProjection_inner_eq_zero x (z - M.starProjection x)
    (M.sub_mem hz (M.starProjection_apply_mem x)), RCLike.zero_re]

theorem double_orthogonal_eq_closure : Spec.DoubleOrthogonalEqClosure.{u, v} := by
  intro 𝕜 H _ _ _ _ L
  exact L.orthogonal_orthogonal_eq_closure

end ExpandedFA.Hilbert.Projection
