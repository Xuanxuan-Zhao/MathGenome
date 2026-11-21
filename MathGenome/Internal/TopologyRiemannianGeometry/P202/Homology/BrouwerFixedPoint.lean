import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.BrouwerFixedPoint
import MathGenome.PointSetTopology.Topics.D10Topology.Ch17

/-!
No-retraction and fixed-point conclusions of paper.tex, Proposition
`prop:p202-degree`. The library proves finite-dimensional Brouwer directly
using Sperner's lemma, and then derives no retraction. We specialize to the
shared Euclidean closed disks and transport the boundary identity between
metric-sphere and unit-norm subtypes. Both results include the interval (n = 0).
-/
namespace P202.BrouwerFixedPoint

/-- No continuous retraction from a closed disk to its boundary. -/
theorem noRetraction : P202Specs.BrouwerFixedPoint.noRetraction_type := by
  intro n ⟨r, hr, hfix⟩
  let b : {x : EuclideanSpace ℝ (Fin (n+1)) // ‖x‖ ≤ 1} →
      P202.Cellular.Disk (n+1) := fun x => ⟨x.val, by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property⟩
  let s : P202.Cellular.Sphere (n+1) →
      {x : EuclideanSpace ℝ (Fin (n+1)) // ‖x‖ = 1} :=
    fun x => ⟨x.val, by simpa only [Metric.mem_sphere, dist_zero_right] using x.property⟩
  have hb : Continuous b := continuous_subtype_val.subtype_mk _
  have hs : Continuous s := continuous_subtype_val.subtype_mk _
  apply D10Topology.Ch17.no_retraction_ball_sphere (n+1) (by omega)
  refine ⟨s ∘ r ∘ b, hs.comp (hr.comp hb), ?_⟩
  intro y
  apply Subtype.ext
  change (r (b ⟨y.val, y.property.le⟩)).val = y.val
  let y' : P202.Cellular.Sphere (n+1) := ⟨y.val, by simpa only [Metric.mem_sphere, dist_zero_right] using y.property⟩
  have heq : b ⟨y.val, y.property.le⟩ =
      P202.Cellular.boundaryInclusion (n+1) y' := Subtype.ext rfl
  rw [heq, hfix]

/-- Brouwer's fixed-point theorem for every positive-dimensional closed disk. -/
theorem fixedPoint : P202Specs.BrouwerFixedPoint.fixedPoint_type := by
  intro n f hf
  exact D10Topology.Ch17.brouwer_euclidean (n+1) (Metric.closedBall 0 1)
    ⟨0, by simp⟩ (isCompact_closedBall 0 1) (convex_closedBall 0 1) f hf

end P202.BrouwerFixedPoint
