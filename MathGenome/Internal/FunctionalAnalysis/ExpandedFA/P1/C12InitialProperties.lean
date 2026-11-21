import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12InitialProperties
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12DualPair
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05Norming
import Mathlib.Analysis.LocallyConvex.WeakDual

/-! Hausdorffness, vector continuity, and real local convexity of the
initial topology of a point-separating bilinear pairing.
Only Hausdorffness needs separation. Neither space is assumed normed.
-/

namespace ExpandedFA.P1.C12InitialProperties

universe u v w
open scoped Topology
noncomputable section

theorem dualPairTopology_hausdorff : Spec.Hausdorff := by
  intro 𝕜 X Y _ _ _ _ _ B hB
  change @T2Space (WeakBilin B.flip) (TopologicalSpace.induced id
    (WeakBilin.instTopologicalSpace B.flip))
  rw [induced_id]
  apply (WeakBilin.isEmbedding (B := B.flip) ?_).t2Space
  exact LinearMap.ker_eq_bot.mp
    (LinearMap.separatingRight_iff_flip_ker_eq_bot.mp hB)

theorem dualPairTopology_continuousAdd :
    Spec.AdditionContinuous := by
  intro 𝕜 X Y _ _ _ _ _ B
  change @ContinuousAdd (WeakBilin B.flip) (TopologicalSpace.induced id
    (WeakBilin.instTopologicalSpace B.flip)) _
  rw [induced_id]
  infer_instance

theorem dualPairTopology_continuousSMul :
    Spec.ScalarMultiplicationContinuous := by
  intro 𝕜 X Y _ _ _ _ _ B
  change @ContinuousSMul 𝕜 (WeakBilin B.flip) _ _ (TopologicalSpace.induced id
    (WeakBilin.instTopologicalSpace B.flip))
  rw [induced_id]
  infer_instance

theorem dualPairTopology_locallyConvex : Spec.LocalConvexity := by
  intro 𝕜 X Y _ _ _ _ _ B
  let := Module.restrictScalars ℝ 𝕜 X
  let := IsScalarTower.restrictScalars ℝ 𝕜 X
  change @LocallyConvexSpace ℝ (WeakBilin B.flip) _ _ _ _ (TopologicalSpace.induced id
    (WeakBilin.instTopologicalSpace B.flip))
  rw [induced_id]
  infer_instance

theorem dualPairTopology_convexBalancedNeighborhoods :
    Spec.ConvexBalancedNeighborhoods := by
  intro 𝕜 X Y _ _ _ _ _ B
  let := Module.restrictScalars ℝ 𝕜 X
  let := IsScalarTower.restrictScalars ℝ 𝕜 X
  change ∀ U ∈ @nhds (WeakBilin B.flip) (TopologicalSpace.induced id
    (WeakBilin.instTopologicalSpace B.flip)) 0, _
  rw [induced_id]
  intro U hU
  obtain ⟨p, hp, hsub⟩ := (LinearMap.weakBilin_withSeminorms B.flip).hasBasis_ball.mem_iff.mp hU
  let q := p.1.sup (B.flip.toSeminormFamily : Y → Seminorm 𝕜 (WeakBilin B.flip))
  refine ⟨q.ball 0 p.2, ?_, q.convex_ball 0 p.2, q.balanced_ball_zero p.2, hsub⟩
  change q.ball 0 p.2 ∈ @nhds (WeakBilin B.flip) (TopologicalSpace.induced id
    (WeakBilin.instTopologicalSpace B.flip)) 0
  rw [induced_id]
  exact (LinearMap.weakBilin_withSeminorms B.flip).hasBasis_ball.mem_of_mem hp


/-!
Continuous scalar tests of an initial pairing topology. Mathlib's
`LinearMap.mem_span_iff_continuous` has precisely the required algebraic
span and initial topology, over every nontrivially normed field. Its proof
extracts a finite set of tests and factors through their finite-dimensional
coordinate map. `RCLike` satisfies its field hypotheses.

For the normed-space specialization, norming Hahn–Banach functionals prove
point separation explicitly. Span induction in the original norm topology
then identifies the weak continuous tests with the original continuous dual.
-/

theorem pairing_continuous_iff_mem_span :
    Spec.ContinuousIffSpan := by
  intro 𝕜 X Y _ _ _ _ _ B g
  rw [dualPairTopology_initial 𝕜 X Y B]
  exact (LinearMap.mem_span_iff_continuous g).symm

theorem pairing_initial_properties :
    Spec.InitialProperties := by
  intro 𝕜 X Y _ _ _ _ _ B hB
  exact ⟨dualPairTopology_hausdorff 𝕜 X Y B hB,
    dualPairTopology_locallyConvex 𝕜 X Y B,
    dualPairTopology_continuousAdd 𝕜 X Y B,
    dualPairTopology_continuousSMul 𝕜 X Y B,
    pairing_continuous_iff_mem_span 𝕜 X Y B⟩

theorem norm_dual_pairing_separates :
    Spec.NormDualSeparates := by
  intro 𝕜 E _ _ _ x hx
  by_contra hne
  obtain ⟨f, _, hf⟩ := C05Norming.norming_functional_nonzero 𝕜 E x hne
  have hz : (‖x‖ : 𝕜) = 0 := hf.symm.trans (hx f)
  have : ‖x‖ = 0 := RCLike.ofReal_eq_zero.mp hz
  exact hne (norm_eq_zero.mp this)

theorem weak_continuous_linear_dual :
    Spec.WeakContinuousDual := by
  intro 𝕜 E _ _ _ g
  rw [pairing_continuous_iff_mem_span 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E) g]
  constructor
  · intro hg
    have hc : Continuous g := by
      induction hg using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨f, rfl⟩ := hf
        exact f.continuous
      | zero => exact continuous_zero
      | add f h _ _ hf hh => exact hf.add hh
      | smul c f _ hf => exact hf.const_smul c
    exact ⟨⟨g, hc⟩, rfl⟩
  · rintro ⟨f, rfl⟩
    exact Submodule.subset_span ⟨f, rfl⟩

theorem weak_initial_properties :
    Spec.WeakInitialProperties := by
  intro 𝕜 E _ _ _
  have h := pairing_initial_properties 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)
    (norm_dual_pairing_separates 𝕜 E)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

end
end ExpandedFA.P1.C12InitialProperties
