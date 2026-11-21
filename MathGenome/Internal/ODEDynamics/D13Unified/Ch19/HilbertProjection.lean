import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.HilbertProjection
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
Closed-subspace projection, paper.tex, Lemma `d13:19:hilbert-projection`.
Closedness in the complete ambient space makes the subspace complete, giving
Mathlib's orthogonal projection. Its residual is orthogonal to the subspace;
the characterization of the projection gives uniqueness of both components.
-/

namespace D13Unified.Ch19.HilbertProjection

/-- A closed subspace of a real or complex Hilbert space and its orthogonal
complement form a direct sum, with unique components for every vector. -/
theorem closed_subspace_projection :
    Specs.D13Unified.Ch19.HilbertProjection.closed_subspace_projection_type := by
  intro 𝕜 H _ _ _ _ M hM
  let : CompleteSpace M := hM.isComplete.completeSpace_coe
  refine ⟨M.isCompl_orthogonal, fun x => ?_⟩
  let m := M.starProjection x
  refine ⟨(m, x - m), ⟨M.starProjection_apply_mem x,
    M.sub_starProjection_mem_orthogonal x, (add_sub_cancel m x).symm⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨ha, hb, hx⟩
  have hm : m = a := M.eq_starProjection_of_mem_orthogonal' ha hb hx
  apply Prod.ext
  · exact hm.symm
  · change b = x - m
    rw [hm, hx, add_sub_cancel_left]

end D13Unified.Ch19.HilbertProjection
