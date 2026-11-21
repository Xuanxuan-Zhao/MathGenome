import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Operations
import Mathlib.Analysis.Normed.Module.Seminorm.Norm

/-! Basic norm estimates and continuity, Proposition `fa2:p1:c01:operations`. -/

namespace ExpandedFA.P1.C01Operations

theorem induced_distance_metric : Spec.InducedDistanceMetric := by
  intro 𝕜 E _ _ _
  exact ⟨dist_eq_norm, fun _ _ => dist_nonneg, fun _ _ => dist_eq_zero,
    dist_comm, dist_triangle⟩

theorem norm_estimates : Spec.NormEstimates := by
  intro 𝕜 E _ _ _
  exact ⟨abs_norm_sub_norm_le, lipschitzWith_one_norm⟩

theorem operations_continuous : Spec.OperationsContinuous := by
  intro 𝕜 E _ _ _
  exact ⟨continuous_fst.add continuous_snd, continuous_fst.smul continuous_snd⟩

theorem translation_homeomorphisms : Spec.TranslationHomeomorphisms := by
  intro 𝕜 E _ _ _ v
  exact ⟨Homeomorph.addLeft v, fun _ => rfl, fun _ => rfl⟩

theorem nonzero_smul_homeomorphisms : Spec.NonzeroSMulHomeomorphisms := by
  intro 𝕜 E _ _ _ a ha
  exact ⟨Homeomorph.smulOfNeZero a ha, fun _ => rfl, fun _ => rfl⟩

theorem subspace_closure_linear : Spec.SubspaceClosureLinear := by
  intro 𝕜 E _ _ _ M
  exact ⟨M.topologicalClosure, M.topologicalClosure_coe⟩

theorem norm_balls_real_convex : Spec.NormBallsRealConvex := by
  intro 𝕜 E _ _ _
  let := NormedSpace.restrictScalars ℝ 𝕜 E
  intro x r _
  exact ⟨convex_ball x r, convex_closedBall x r⟩

theorem zero_balls_balanced : Spec.ZeroBallsBalanced := by
  intro 𝕜 E _ _ _ r _
  exact ⟨fun _ ha _ hy => balanced_iff_smul_mem.mp (balanced_ball_zero (𝕜 := 𝕜)) ha hy,
    fun _ ha _ hy => balanced_iff_smul_mem.mp (balanced_closedBall_zero (𝕜 := 𝕜)) ha hy⟩

end ExpandedFA.P1.C01Operations
