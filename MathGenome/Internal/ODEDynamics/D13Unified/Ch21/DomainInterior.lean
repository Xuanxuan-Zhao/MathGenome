import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch21.DomainInterior
import MathGenome.Internal.ODEDynamics.D13Unified.Ch21.SmoothJordan
import MathGenome.Internal.ODEDynamics.D13Unified.Ch21.IndexProperties

/-! Interior containment uses free loop contractibility and the nonzero
index on the Jordan interior. No convexity assumption on the domain is used. -/
namespace D13Unified.Ch21.DomainInterior
noncomputable section
open Set unitInterval
open Specs.D13Unified.Ch21.Collar
open Specs.D13Unified.Ch21.IndexProperties
open Specs.D13Unified.Ch21.SmoothJordan

abbrev SourceSimplyConnected := Specs.D13Unified.Ch21.DomainInterior.SourceSimplyConnected
abbrev BoundedInterior := Specs.D13Unified.Ch21.DomainInterior.BoundedInterior

theorem library_simply_connected_iff :
    Specs.D13Unified.Ch21.DomainInterior.library_simply_connected_iffStatement := by
  intro U
  exact isSimplyConnected_iff_exists_homotopy_refl_forall_mem

theorem library_implies_source :
    Specs.D13Unified.Ch21.DomainInterior.library_implies_sourceStatement := by
  intro U hU
  obtain ⟨hpath, hcontract⟩ := library_simply_connected_iff U |>.mp hU
  refine ⟨hpath, ?_⟩
  intro α hα
  let a : Path (α 0) (α 0) :=
    { toContinuousMap := α.map
      source' := rfl
      target' := α.closed.symm }
  obtain ⟨H, hH⟩ := hcontract (α 0) a (fun t => hα ⟨t, rfl⟩)
  refine ⟨α 0, hα ⟨0, rfl⟩, H.toHomotopy.toContinuousMap, ?_, ?_, ?_, ?_⟩
  · intro t
    exact H.apply_zero t
  · intro t
    exact H.apply_one t
  · intro s
    exact (H.source s).trans (H.target s).symm
  · intro s t
    exact hH (s, t)

/-- A contraction inside U avoids every point outside U, so homotopy
invariance identifies the index with that of a constant loop. -/
theorem index_zero_outside_domain :
    Specs.D13Unified.Ch21.DomainInterior.index_zero_outside_domainStatement := by
  intro U hU α hα p hp
  obtain ⟨z, hz, H, h0, h1, hc, hH⟩ := hU.2 α hα
  let β : Loop := ⟨ContinuousMap.const I z, rfl⟩
  have he : index α p = index β p :=
    IndexProperties.homotopy_invariant α β p H h0 h1 hc
      (fun s t he => hp (he ▸ hH s t))
  exact he.trans (IndexProperties.constant_loop_index z p (fun he => hp (he ▸ hz)))

/-- Identification with the bounded Jordan component uses the actual
connected-component equations and boundedness; no index is assumed. -/
theorem domain_interior :
    Specs.D13Unified.Ch21.DomainInterior.domain_interiorStatement := by
  intro U _hU hsc γ hγ htrace Ω hΩ
  obtain ⟨V, E, hcomp, _hVo, _hEo, _hVp, _hEp, _hVb, hEb, _hVf, _hEf,
    hcl, _hC1, _hiE, k, hk, hiV⟩ := SmoothJordan.smooth_jordan γ hγ
  have hVU : V ⊆ U := by
    intro p hp
    by_contra hpU
    have hloop : range (circleLoop (regularLoopMap γ hγ)) ⊆ U := by
      rw [IndexProperties.circle_trace]
      exact htrace
    have hi0 := index_zero_outside_domain U hsc _ hloop p hpU
    have hk0 : k = 0 := (hiV p hp).symm.trans hi0
    rcases hk with hk | hk <;> omega
  have hΩV : Ω = V := by
    obtain ⟨p, hp, hpΩ, hΩb⟩ := hΩ
    have hpVE : p ∈ V ∪ E := hcomp.2.2.2.1.symm ▸ hp
    rcases hpVE with hpV | hpE
    · exact hpΩ.symm.trans (hcomp.2.2.2.2.1 p hpV)
    · have hΩE : Ω = E := hpΩ.symm.trans (hcomp.2.2.2.2.2 p hpE)
      exact False.elim (hEb (hΩE ▸ hΩb))
  subst Ω
  refine ⟨hVU, ?_⟩
  rw [hcl]
  exact union_subset hVU htrace

theorem exists_domain_interior :
    Specs.D13Unified.Ch21.DomainInterior.exists_domain_interiorStatement := by
  intro U hU hsc γ hγ htrace
  obtain ⟨Ω, E, hcomp, _hΩo, _hEo, _hΩp, _hEp, hΩb, _rest⟩ :=
    SmoothJordan.smooth_jordan γ hγ
  obtain ⟨p, hp⟩ := hcomp.1
  have hpS : p ∈ (range γ)ᶜ := hcomp.2.2.2.1 ▸ Or.inl hp
  have hΩ : BoundedInterior γ Ω :=
    ⟨p, hpS, hcomp.2.2.2.2.1 p hp, hΩb⟩
  exact ⟨Ω, hΩ, domain_interior U hU hsc γ hγ htrace Ω hΩ⟩

theorem domain_interior_of_isSimplyConnected :
    Specs.D13Unified.Ch21.DomainInterior.domain_interior_of_isSimplyConnectedStatement := by
  intro U hU hsc
  exact domain_interior U hU (library_implies_source U hsc)

end
end D13Unified.Ch21.DomainInterior
