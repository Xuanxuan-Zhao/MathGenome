import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.BoundaryMaximum
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.MeanValueStrongPrinciple
import Mathlib.Topology.Connected.Clopen

noncomputable section
open Set Metric Complex
open scoped Topology

namespace D12Complex.BoundaryMaximum

abbrev BoundaryLimsupLE : Specs.D12Complex.Ch13.BoundaryMaximum.BoundaryLimsupLE_type :=
  _root_.D12Complex.BoundaryLimsupLE

abbrev BoundaryLiminfGE : Specs.D12Complex.Ch13.BoundaryMaximum.BoundaryLiminfGE_type :=
  _root_.D12Complex.BoundaryLiminfGE

/-- A superlevel strictly above the boundary upper bound stays inside the
open set. This uses only the boundary limit condition. -/
lemma closure_superlevel_subset {U : Set ℂ} {u : ℂ → ℝ} {M t : ℝ}
    (hU : IsOpen U) (hb : BoundaryLimsupLE U u M) (ht : M < t) :
    closure {z ∈ U | t ≤ u z} ⊆ U := by
  intro ξ hξ
  by_contra hn
  have hf : ξ ∈ frontier U := by
    rw [hU.frontier_eq]
    exact ⟨closure_mono (fun z hz => hz.1) hξ, hn⟩
  obtain ⟨δ, hδ, hbound⟩ := hb ξ hf ((t - M) / 2) (by linarith)
  obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.mp hξ δ hδ
  have := hbound z hz.1 (by simpa [dist_comm] using hdist)
  linarith [hz.2]

/-- Boundary limits make every strict superlevel compact; no boundary
extension of the function is used. -/
lemma isCompact_superlevel {U : Set ℂ} {u : ℂ → ℝ} {M t : ℝ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hc : ContinuousOn u U)
    (hb : BoundaryLimsupLE U u M) (ht : M < t) :
    IsCompact {z ∈ U | t ≤ u z} := by
  let K := {z ∈ U | t ≤ u z}
  have hsub : closure K ⊆ U := closure_superlevel_subset hU hb ht
  have hclosed : IsClosed (closure K ∩ u ⁻¹' Ici t) :=
    (hc.mono hsub).preimage_isClosed_of_isClosed isClosed_closure isClosed_Ici
  have heq : closure K ∩ u ⁻¹' Ici t = K := by
    ext z
    exact ⟨fun hz => ⟨hsub hz.1, hz.2⟩,
      fun hz => ⟨subset_closure hz, hz.2⟩⟩
  rw [heq] at hclosed
  exact isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hUb.subset (fun z hz => hz.1)⟩

theorem continuous_mean_boundary_maximum :
    Specs.D12Complex.Ch13.BoundaryMaximum.continuous_mean_boundary_maximum_type := by
  intro U u M hU hUb hc hm hb z hz
  by_contra hn
  have hzt : M < u z := lt_of_not_ge hn
  obtain ⟨a, ha, hmax⟩ := (isCompact_superlevel hU hUb hc hb hzt).exists_isMaxOn
    ⟨z, hz, le_rfl⟩ (hc.mono (fun w hw => hw.1))
  have hglobal : ∀ w ∈ U, u w ≤ u a := by
    intro w hw
    by_cases ht : u z ≤ u w
    · exact hmax ⟨hw, ht⟩
    · exact (le_of_not_ge ht).trans ha.2
  let K : Set ℂ := {w ∈ U | u a ≤ u w}
  have hKc : IsCompact K := isCompact_superlevel hU hUb hc hb (hzt.trans_le ha.2)
  have hKo : IsOpen K := by
    apply isOpen_iff_mem_nhds.mpr
    intro w hw
    obtain ⟨ρ, hρ, hsub, heq⟩ := MeanValueStrongPrinciple.maximum_locally_constant hc hm hw.1
      (fun v hv => (hglobal v hv).trans hw.2)
    apply Filter.mem_of_superset (ball_mem_nhds w hρ)
    intro v hv
    exact ⟨hsub hv, hw.2.trans_eq (heq v hv).symm⟩
  have heq : K = univ := (show IsClopen K from ⟨hKc.isClosed, hKo⟩).eq_univ
    ⟨a, ha.1, le_rfl⟩
  exact NormedSpace.unbounded_univ ℝ ℂ (heq ▸ hKc.isBounded)

/-- Sign reversal preserves the local circle mean property. -/
lemma localCircleMeanProperty_neg {U : Set ℂ} {u : ℂ → ℝ}
    (hm : LocalCircleMeanProperty U u) : LocalCircleMeanProperty U (fun z => -u z) := by
  intro a ha
  obtain ⟨ρ, hρ, hsub, hmean⟩ := hm a ha
  refine ⟨ρ, hρ, hsub, fun r hr hrρ => ?_⟩
  simpa [Real.circleAverage] using congrArg Neg.neg (hmean r hr hrρ)

theorem continuous_mean_boundary_minimum :
    Specs.D12Complex.Ch13.BoundaryMaximum.continuous_mean_boundary_minimum_type := by
  intro U u m hU hUb hc hm hb z hz
  have hbneg : BoundaryLimsupLE U (fun w => -u w) (-m) := by
    intro ξ hξ ε hε
    obtain ⟨δ, hδ, hbound⟩ := hb ξ hξ ε hε
    refine ⟨δ, hδ, fun w hw hd => ?_⟩
    have := hbound w hw hd
    linarith
  have := continuous_mean_boundary_maximum U (fun w => -u w) (-m)
    hU hUb hc.neg (localCircleMeanProperty_neg hm) hbneg z hz
  linarith

theorem harmonic_boundary_maximum :
    Specs.D12Complex.Ch13.BoundaryMaximum.harmonic_boundary_maximum_type := by
  intro U u M hUb hu hb
  exact continuous_mean_boundary_maximum U u M hu.1 hUb hu.2.1.continuousOn
    (MeanValueStrongPrinciple.harmonic_local_circle_mean U u hu) hb

theorem harmonic_boundary_minimum :
    Specs.D12Complex.Ch13.BoundaryMaximum.harmonic_boundary_minimum_type := by
  intro U u m hUb hu hb
  exact continuous_mean_boundary_minimum U u m hu.1 hUb hu.2.1.continuousOn
    (MeanValueStrongPrinciple.harmonic_local_circle_mean U u hu) hb

end D12Complex.BoundaryMaximum
