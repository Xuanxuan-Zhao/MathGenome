import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C13Subsequences
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13Alaoglu
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13Metric
import Mathlib.Topology.Sequences

namespace ExpandedFA.P1.C13Subsequences

open scoped Topology
open Topology

/-- Compactness plus bounded-ball metrizability gives weak-star subsequences.
Only the predual is assumed separable, and it may be incomplete. -/
theorem weakStar_subsequence : Spec.SubsequenceConvergence := by
  intro 𝕜 E _ _ _ _ f hf
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hf
  let A : Set (E →L[𝕜] 𝕜) := Metric.closedBall 0 (max R 0)
  have hmem : ∀ n, f n ∈ A := by
    intro n
    simp only [A, Metric.mem_closedBall, dist_zero_right]
    exact (hR (f n) (Set.mem_range_self n)).trans (le_max_left _ _)
  have hb : Bornology.IsBounded A := Metric.isBounded_closedBall
  obtain ⟨x, hx⟩ := C13Metric.dense_tests_exist 𝕜 E
  obtain ⟨m, _hdist, htop⟩ := C13Metric.bounded_weakStar_metric 𝕜 E x hx A hb
  let tw := C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E
  have hc : @IsCompact (E →L[𝕜] 𝕜) tw A := by
    simpa only [A, Metric.closedBall, dist_eq_norm, sub_zero] using
      C13Alaoglu.weakStar_closedBall_isCompact 𝕜 E 0 (max R 0) (le_max_right _ _)
  have hca : @CompactSpace A (TopologicalSpace.induced Subtype.val tw) :=
    isCompact_iff_compactSpace.mp hc
  have hcm : @CompactSpace A m.toUniformSpace.toTopologicalSpace := by
    rw [htop]
    exact hca
  let : MetricSpace A := m
  let : PseudoMetricSpace A := m.toPseudoMetricSpace
  let : TopologicalSpace A := m.toUniformSpace.toTopologicalSpace
  let : CompactSpace A := hcm
  obtain ⟨g, k, hk, hlim⟩ := CompactSpace.tendsto_subseq (fun n => (⟨f n, hmem n⟩ : A))
  refine ⟨k, hk, g.val, ?_⟩
  have hcont : @Continuous A (E →L[𝕜] 𝕜)
      m.toUniformSpace.toTopologicalSpace tw Subtype.val := by
    rw [htop]
    exact continuous_induced_dom
  exact (hcont.tendsto g).comp hlim

end ExpandedFA.P1.C13Subsequences
