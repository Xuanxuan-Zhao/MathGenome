import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch18.EvaluationFailure
import MathGenome.Internal.PointSetTopology.D10Topology.Ch13.FunctionTopologies
import MathGenome.Internal.PointSetTopology.D10Topology.Ch11.RationalsNotLocallyCompact
import Mathlib.Topology.UrysohnsLemma

open Set Filter Topology

namespace D10Topology.Ch18

/-- A compact control set cannot control evaluation near the rational origin.
Urysohn separation supplies the same zero-on-K, value-two-at-y witness as
the distance formula in the paper, including when K is empty. -/
theorem rational_compact_control_escape (K : Set ℚ) (hK : IsCompact K)
    (U : Set ℚ) (hU : U ∈ 𝓝 (0 : ℚ)) :
    ∃ y ∈ U, ∃ h : C(ℚ, ℝ), EqOn h 0 K ∧ h y = 2 := by
  have hn : ¬ U ⊆ K := fun hsub =>
    Ch11.rational_no_compact_neighborhood 0 K hK (mem_of_superset hU hsub)
  obtain ⟨y, hyU, hyK⟩ := Set.not_subset.mp hn
  obtain ⟨g, hgK, hgy, -⟩ := exists_continuous_zero_one_of_isClosed
    hK.isClosed (isClosed_singleton (x := y)) (disjoint_singleton_right.mpr hyK)
  refine ⟨y, hyU, ContinuousMap.const ℚ (2 : ℝ) * g, ?_, ?_⟩
  · intro x hx
    simp [hgK hx]
  · simp [hgy (mem_singleton y)]

theorem evaluation_failure : Specs.D10Topology.Ch18.EvaluationFailure.evaluation_failure := by
  unfold Specs.D10Topology.Ch18.EvaluationFailure.evaluation_failure
  have ht : Specs.D10Topology.Ch13.FunctionTopologies.compactOpenContinuousTopology
      (X := ℚ) (Y := ℝ) = ContinuousMap.compactOpen :=
    Ch13.compactOpenContinuousTopology_eq_mathlib
  rw [ht]
  intro hc
  have hN : {p : C(ℚ, ℝ) × ℚ | p.1 p.2 ∈ Iio (1 : ℝ)} ∈
      𝓝 ((0 : C(ℚ, ℝ)), (0 : ℚ)) :=
    hc.preimage_mem_nhds (isOpen_Iio.mem_nhds (by norm_num))
  obtain ⟨N, hN, U, hU, hNU⟩ := mem_nhds_prod_iff.mp hN
  have hb := (nhds_basis_opens (0 : ℝ)).nhds_continuousMapConst (X := ℚ)
  obtain ⟨⟨K, V⟩, ⟨hK, hV⟩, hsub⟩ := hb.mem_iff.mp hN
  obtain ⟨y, hyU, h, hhK, hhy⟩ := rational_compact_control_escape K hK U hU
  have hhN : h ∈ N := hsub (by
    intro x hx
    simpa [hhK hx] using hV.1)
  have hlt : h y < 1 := hNU (show (h, y) ∈ N ×ˢ U from ⟨hhN, hyU⟩)
  rw [hhy] at hlt
  norm_num at hlt

end D10Topology.Ch18
