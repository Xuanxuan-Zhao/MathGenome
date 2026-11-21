import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.ContinuousPathGeometry

/-! Geometry of continuous paths on a compact real time interval.

`ContinuousMap.instMetricSpace` is pulled back from bounded continuous
functions. Its distance is the supremum distance and its topology is the
pre-existing compact-open topology. Compactness of the domain makes every
continuous path bounded; the state space itself need not be bounded.
-/

namespace ProbabilityFoundations.Ch05

theorem uniformDistance : Specs.UniformDistance := by
  intro S _ _ _ T _ f g
  exact ContinuousMap.dist_eq_iSup

theorem uniformDistance_finite : Specs.UniformDistanceFinite := by
  intro S _ _ _ T _ f g
  exact ⟨dist f g, dist_nonneg, fun t => ContinuousMap.dist_apply_le_dist t⟩

theorem uniformMetric_topology : Specs.UniformMetricTopology := by
  intro S _ _ _ T _
  rfl

theorem pathSpace_separable : Specs.PathSpaceSeparable := by
  intro S _ _ _ T _
  infer_instance

theorem pathSpace_complete : Specs.PathSpaceComplete := by
  intro S _ _ _ _ T _
  infer_instance

end ProbabilityFoundations.Ch05
