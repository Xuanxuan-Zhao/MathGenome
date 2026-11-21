import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Ergodic.DiscreteMeanErgodic
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Adjoint
import Mathlib.Analysis.InnerProductSpace.MeanErgodic

/-!
The discrete mean ergodic theorem on arbitrary real or complex Hilbert spaces.
Mathlib's contraction theorem gives convergence to the fixed-space projector;
the final proof identifies its equalizer and iterates with the kernel and
operator powers in the source. The adjoint fixed-space identity follows from
the equality case of the Hilbert norm/inner-product inequality. The accepted
adjoint range theorem then identifies the orthogonal summand.
-/

noncomputable section
open scoped Topology InnerProductSpace

namespace ExpandedFA.Ergodic.DiscreteMeanErgodic
universe u v

theorem kernel_fixed_points : Spec.KernelFixedPoints.{u, v} := by
  intro 𝕜 H _ _ _ T x
  change x - T x = 0 ↔ T x = x
  exact sub_eq_zero.trans eq_comm

private theorem adjoint_fixes_of_fixes
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H →L[𝕜] H) (hT : ‖T‖ ≤ 1) {x : H} (hx : T x = x) :
    T.adjoint x = x := by
  apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := 𝕜)
  · have hTa : ‖T.adjoint‖ ≤ 1 := by
      simpa only [ContinuousLinearMap.adjoint.norm_map] using hT
    simpa only [one_mul] using T.adjoint.le_of_opNorm_le hTa x
  · simp [ContinuousLinearMap.adjoint_inner_left, hx]

theorem fixed_spaces : Spec.FixedSpaces.{u, v} := by
  intro 𝕜 H _ _ _ _ T hT
  change (1 - T).ker = (1 - T.adjoint).ker
  ext x
  rw [kernel_fixed_points 𝕜 H, kernel_fixed_points 𝕜 H]
  constructor
  · exact adjoint_fixes_of_fixes T hT
  · intro hx
    have hTa : ‖T.adjoint‖ ≤ 1 := by
      simpa only [ContinuousLinearMap.adjoint.norm_map] using hT
    simpa only [ContinuousLinearMap.adjoint_adjoint] using
      adjoint_fixes_of_fixes T.adjoint hTa hx

theorem range_closure : Spec.RangeClosure.{u, v} := by
  intro 𝕜 H _ _ _ _ T hT
  have h := Hilbert.Adjoint.range_closure_eq_orthogonal_adjoint_ker 𝕜 H H (1 - T)
  change (1 - T).range.topologicalClosure = _ at h
  have hfix : (1 - T).ker = (1 - T.adjoint).ker := fixed_spaces 𝕜 H T hT
  simpa only [Hilbert.Adjoint.Spec.AdjointValue, map_sub,
    ContinuousLinearMap.adjoint_one, ← hfix] using h

theorem orthogonal_decomposition : Spec.OrthogonalDecomposition.{u, v} := by
  intro 𝕜 H _ _ _ _ T hT
  rw [range_closure 𝕜 H T hT]
  exact Hilbert.Projection.closed_subspace_decomposition 𝕜 H (1 - T).ker
    (1 - T).isClosed_ker

theorem strong_convergence : Spec.StrongConvergence.{u, v} := by
  intro 𝕜 H _ _ _ _ T hT x
  have hfix : T.eqLocus (1 : H →L[𝕜] H) = (1 - T).ker := by
    ext y
    change T y = y ↔ y - T y = 0
    exact eq_comm.trans sub_eq_zero.symm
  have h := T.tendsto_birkhoffAverage_orthogonalProjection hT x
  change Filter.Tendsto _ _
    (𝓝 ((T.eqLocus (1 : H →L[𝕜] H)).starProjection x)) at h
  simpa only [birkhoffAverage, birkhoffSum, id_eq,
    smul_apply, sum_apply,
    FunLike.coe_pow_eq_iterate, Hilbert.Conventions.Spec.OrthogonalProjectionValue,
    hfix] using h

end ExpandedFA.Ergodic.DiscreteMeanErgodic
