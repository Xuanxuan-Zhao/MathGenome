import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch17.NoRetraction
import MathGenome.Internal.PointSetTopology.D10Topology.Ch17.BrouwerConvex
import Mathlib.Analysis.Normed.Module.Convex

/-! The no-retraction corollary of finite-dimensional Brouwer.
The negative of a proposed retraction is a continuous self-map of the ball.
Its Brouwer fixed point belongs to the sphere, where the retraction is the
identity. This forces that point to be zero, contradicting its unit norm. -/
namespace D10Topology.Ch17

theorem no_retraction_ball_sphere :
    Specs.D10Topology.Ch17.NoRetraction.no_retraction_ball_sphere := by
  intro n _ ⟨r, hr, hfix⟩
  let B : Set (EuclideanSpace ℝ (Fin n)) := {x | ‖x‖ ≤ 1}
  have hB : B = Metric.closedBall 0 1 := by
    ext x
    simp [B, Metric.mem_closedBall, dist_zero_right]
  have hne : B.Nonempty := ⟨0, by simp [B]⟩
  have hcompact : IsCompact B := by
    rw [hB]
    exact isCompact_closedBall 0 1
  have hconvex : Convex ℝ B := by
    rw [hB]
    exact convex_closedBall 0 1
  let f : B → B := fun x => ⟨-(r x).val, by simp [(r x).property, B]⟩
  have hf : Continuous f :=
    ((continuous_subtype_val.comp hr).neg).subtype_mk _
  obtain ⟨x, hx⟩ := brouwer_euclidean n B hne hcompact hconvex f hf
  have hxeq : -(r x).val = x.val := congrArg Subtype.val hx
  have hxnorm : ‖x.val‖ = 1 := by
    rw [← hxeq, norm_neg]
    exact (r x).property
  let y : {z : EuclideanSpace ℝ (Fin n) // ‖z‖ = 1} := ⟨x.val, hxnorm⟩
  have hrx : (r x).val = x.val := by
    have h := congrArg Subtype.val (hfix y)
    exact h
  have hxzero : x.val = 0 := by
    have heq : x.val + x.val = 0 := by
      calc
        x.val + x.val = -(r x).val + x.val := congrArg (fun z => z + x.val) hxeq.symm
        _ = 0 := by rw [hrx]; exact neg_add_cancel _
    have hsmul : (2 : ℝ) • x.val = 0 := by simpa [two_smul ℝ] using heq
    exact (smul_eq_zero.mp hsmul).resolve_left (by norm_num)
  simp [hxzero] at hxnorm

end D10Topology.Ch17
