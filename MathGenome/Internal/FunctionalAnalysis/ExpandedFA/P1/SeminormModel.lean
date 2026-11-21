import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.SeminormModel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.BalancedBounded
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06GaugeProperties

/-! The seminorm model of Hausdorff locally convex spaces, over ℝ or ℂ.
Local convexity always refers to the compatible underlying real module. -/

open Set Filter
open scoped Topology

namespace ExpandedFA.P1

def seminormTopology : SeminormModelSpec.topologyType := SeminormModelSpec.topologyValue

section Basis
variable {𝕜 E ι : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- A finite maximum ball is exactly the source's finite intersection. -/
theorem seminorm_basicSet_eq_ball (p : SeminormFamily 𝕜 E ι) (s : Finset ι)
    {r : ℝ} (hr : 0 < r) :
    {x : E | ∀ i ∈ s, p i x < r} = (s.sup p).ball 0 r := by
  ext x
  simp only [Seminorm.ball_finset_sup_eq_iInter p s 0 hr,
    mem_iInter, Seminorm.mem_ball_zero, mem_ofPred_eq]

theorem seminorm_neighborhood_basis [TopologicalSpace E] (p : SeminormFamily 𝕜 E ι)
    (hp : WithSeminorms p) :
    (𝓝 (0 : E)).HasBasis (fun sr : Finset ι × ℝ => 0 < sr.2)
      (fun sr => {x : E | ∀ i ∈ sr.1, p i x < sr.2}) := by
  refine ⟨fun U => ?_⟩
  rw [hp.hasBasis_zero_ball.mem_iff]
  exact exists_congr fun sr => and_congr_right fun hr => by
    rw [seminorm_basicSet_eq_ball p sr.1 hr]

end Basis

theorem seminorm_topology_construction : SeminormModelSpec.Construction := by
  intro 𝕜 E ι _ _ _ _ _ p hsep
  let : TopologicalSpace E := seminormTopology 𝕜 E ι p
  have hp : WithSeminorms p := ⟨rfl⟩
  let : IsTopologicalAddGroup E := hp.isTopologicalAddGroup
  let : T1Space E := hp.T1_of_separating hsep
  have hT2 : T2Space E := inferInstance
  exact ⟨⟨⟨hp.isTopologicalAddGroup, hp.continuousSMul⟩, hp.toLocallyConvexSpace⟩,
    hT2, seminorm_neighborhood_basis p hp, hp.continuous_seminorm⟩

theorem seminorm_topology_characterization :
    SeminormModelSpec.TopologyCharacterization := by
  intro 𝕜 E ι _ _ _ t _ p
  constructor
  · intro hb
    have hp : WithSeminorms p := by
      apply SeminormFamily.withSeminorms_of_hasBasis
      refine ⟨fun U => ?_⟩
      rw [hb.mem_iff]
      constructor
      · rintro ⟨⟨s, r⟩, hr, hs⟩
        exact ⟨(s.sup p).ball 0 r, SeminormFamily.basisSets_mem p s hr,
          (seminorm_basicSet_eq_ball p s hr).symm.subset.trans hs⟩
      · rintro ⟨V, hV, hVU⟩
        obtain ⟨s, r, hr, rfl⟩ := (SeminormFamily.basisSets_iff p).mp hV
        exact ⟨(s, r), hr, (seminorm_basicSet_eq_ball p s hr).subset.trans hVU⟩
    exact hp.withSeminorms_eq
  · intro ht
    exact seminorm_neighborhood_basis p ⟨ht⟩

/-- Gauges of open balanced real-convex neighborhoods supply enough continuous
seminorms over the original scalar field to recover the topology. -/
theorem with_continuous_seminorms {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [T2Space E] (hE : LCS 𝕜 E) :
    WithSeminorms (fun q : {q : Seminorm 𝕜 E // Continuous q} => q.1) := by
  let : IsTopologicalAddGroup E := hE.1.1
  let : ContinuousSMul 𝕜 E := hE.1.2
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  let p : SeminormFamily 𝕜 E {q : Seminorm 𝕜 E // Continuous q} := fun q => q.1
  apply SeminormFamily.withSeminorms_of_hasBasis
  refine ⟨fun U => ⟨fun hU => ?_, fun hU => ?_⟩⟩
  · obtain ⟨V, hV, ho, hb, hc, hVU⟩ :=
      absolutely_convex_neighborhood_basis 𝕜 E hE.2 U hU
    have h0 : (0 : E) ∈ V := mem_of_mem_nhds hV
    obtain ⟨⟨q, hq, hcont⟩, _⟩ := C06.minkowskiGauge_continuous_seminorm V hc h0 ho hb
    have heq : q.ball 0 1 = V := by
      rw [Seminorm.ball_zero_eq, C06.minkowskiGauge_open_unit V hc h0 ho]
      ext x
      simp only [mem_ofPred_eq, hq]
    refine ⟨q.ball 0 1, p.basisSets_singleton_mem ⟨q, hcont⟩ one_pos, ?_⟩
    exact heq ▸ hVU
  · obtain ⟨V, hV, hVU⟩ := hU
    exact mem_of_superset (p.basisSets_mem_nhds (fun q => q.2) V hV) hVU

theorem continuous_seminorms_model : SeminormModelSpec.ContinuousSeminormsModel := by
  intro 𝕜 E _ _ _ _ _ _ _ hE
  have hp := with_continuous_seminorms hE
  exact ⟨hp.withSeminorms_eq, hp.separating_of_T1,
    seminorm_neighborhood_basis _ hp⟩

theorem linear_continuous_iff_seminorm_bound : SeminormModelSpec.LinearContinuity := by
  intro 𝕜 E F _ _ _ _ _ _ _ _ _ _ _ _ _ hE hF T
  let : IsTopologicalAddGroup E := hE.1.1
  let : IsTopologicalAddGroup F := hF.1.1
  constructor
  · intro hT q hq
    classical
    refine ⟨{q.comp T}, ?_, 1, one_pos, ?_⟩
    · intro p hp
      have hp' : p = q.comp T := Finset.mem_singleton.mp hp
      subst p
      exact hq.comp hT
    · intro x
      simp only [Finset.sup_singleton, id_eq, one_mul, Seminorm.comp_apply, le_refl]
  · intro h
    apply (with_continuous_seminorms hF).continuous_of_continuous_comp T
    intro q
    obtain ⟨s, hs, C, hC, hbound⟩ := h q.1 q.2
    let c : NNReal := ⟨C, hC.le⟩
    have hdom : Continuous (s.sup id : Seminorm 𝕜 E) :=
      Seminorm.continuous_finsetSup hs
    exact Seminorm.continuous_of_le (q := c • (s.sup id : Seminorm 𝕜 E))
      (hdom.const_smul c) hbound

end ExpandedFA.P1
