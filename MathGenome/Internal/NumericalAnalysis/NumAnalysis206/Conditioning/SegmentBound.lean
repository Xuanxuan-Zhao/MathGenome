import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Conditioning.SegmentBound
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Instances.ENNReal.Lemmas

open Set

namespace NumAnalysis206.Conditioning

/-- Continuity at the endpoints and a derivative bound only along the
interior of a real segment imply the finite forward error estimate.
The scalar field may be real or complex; no completeness or dimension
hypothesis is needed. -/
theorem segment_forward_bound : Specs.NumAnalysis206.Conditioning.segmentForwardBoundType := by
  intro 𝕜 _ X Y _ _ _ _ f D x v L
  let : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  intro hL hc hd hb
  by_cases hv : v = 0
  · simp [hv]
  have hne : x ≠ x + v := by
    intro h
    apply hv
    simpa using (congrArg (fun z : X => z - x) h).symm
  have hinterior (z : X) (hz : z ∈ openSegment ℝ x (x + v)) :
      z ∈ segment ℝ x (x + v) ∧ z ≠ x ∧ z ≠ x + v := by
    refine ⟨openSegment_subset_segment ℝ x (x + v) hz, ?_, ?_⟩
    · intro he
      subst z
      exact hne (left_mem_openSegment_iff.mp hz)
    · intro he
      subst z
      exact hne (right_mem_openSegment_iff.mp hz)
  -- Apply the convex mean value estimate only on the open segment.
  have hlip : LipschitzOnWith ⟨L, hL⟩ f (openSegment ℝ x (x + v)) := by
    apply (convex_openSegment x (x + v)).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (f' := D)
    · intro z hz
      obtain ⟨hzs, hzx, hzy⟩ := hinterior z hz
      exact (hd z hzs hzx hzy).mono (openSegment_subset_segment ℝ x (x + v))
    · intro z hz
      obtain ⟨hzs, hzx, hzy⟩ := hinterior z hz
      exact hb z hzs hzx hzy
  -- The endpoint estimate follows from continuity, not endpoint differentiability.
  have hclosed : LipschitzOnWith ⟨L, hL⟩ f (segment ℝ x (x + v)) := by
    have hc' : ContinuousOn f (closure (openSegment ℝ x (x + v))) := by
      simpa only [closure_openSegment] using hc
    simpa only [closure_openSegment] using LipschitzOnWith.closure hc' hlip
  have h := (lipschitzOnWith_iff_norm_sub_le.mp hclosed)
    (right_mem_segment ℝ x (x + v)) (left_mem_segment ℝ x (x + v))
  change ‖f (x + v) - f x‖ ≤ L * ‖(x + v) - x‖ at h
  simpa only [add_sub_cancel_left] using h

end NumAnalysis206.Conditioning
