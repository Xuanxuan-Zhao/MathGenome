import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch06.BoundaryModulus
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch06.StrongModulus
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.Compact

open Set Filter
open scoped Topology

namespace D12Complex.BoundaryModulus

/-- A nonempty bounded plane domain has a boundary point. -/
private theorem boundary_nonempty {Ω : Set ℂ} (hΩ : IsDomain Ω)
    (hb : Bornology.IsBounded Ω) : (frontier Ω).Nonempty := by
  apply nonempty_frontier_iff.mpr
  refine ⟨hΩ.1, ?_⟩
  intro heq
  have := hb.isCompact_closure.ne_univ
  simp [heq] at this

/-- Boundary limsup bounds, without any continuous boundary extension. -/
theorem norm_le_of_boundary_limsup :
    Specs.D12Complex.Ch06.BoundaryModulus.norm_le_of_boundary_limsup_type := by
  intro Ω f M hΩ hb hf _ hlim z hz
  by_contra hn
  have hMz : M < ‖f z‖ := lt_of_not_ge hn
  obtain ⟨c, hMc, hcz⟩ := exists_between hMz
  let K : Set ℂ := {w | w ∈ Ω ∧ c ≤ ‖f w‖}
  have hKΩ : K ⊆ Ω := fun w hw => hw.1
  -- The limsup bound excludes boundary points from the closure of K.
  have hcl : closure K ⊆ Ω := by
    intro w hw
    by_contra hwΩ
    have hwfront : w ∈ frontier Ω := by
      rw [frontier, hf.1.interior_eq]
      exact ⟨closure_mono hKΩ hw, hwΩ⟩
    have hev : ∀ᶠ v in 𝓝 w, v ∈ Ω → ‖f v‖ < c := by
      simpa only [add_sub_cancel] using
        (eventually_nhdsWithin_iff.mp (hlim w hwfront (c - M) (sub_pos.mpr hMc)))
    obtain ⟨v, hvK, hv⟩ := ((mem_closure_iff_frequently.mp hw).and_eventually hev).exists
    exact (not_lt_of_ge hvK.2) (hv hvK.1)
  have hcK : IsCompact (closure K) :=
    (hb.subset hKΩ).isCompact_closure
  have hcont : ContinuousOn (fun w => ‖f w‖) (closure K) :=
    fun w hw => ((hf.2 w (hcl hw)).continuousAt.norm).continuousWithinAt
  obtain ⟨a, ha, hmax⟩ := hcK.exists_isMaxOn
    ⟨z, subset_closure ⟨hz, hcz.le⟩⟩ hcont
  have hza : ‖f z‖ ≤ ‖f a‖ := hmax (subset_closure ⟨hz, hcz.le⟩)
  have hglobal : ∀ w ∈ Ω, ‖f w‖ ≤ ‖f a‖ := by
    intro w hw
    by_cases hcw : c ≤ ‖f w‖
    · exact hmax (subset_closure ⟨hw, hcw⟩)
    · exact (lt_of_not_ge hcw).le.trans (hcz.le.trans hza)
  have hlocal : IsLocalMaxOn (fun w => ‖f w‖) Ω a := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact hglobal w hw
  have heq := StrongModulus.constant_of_local_maximum_modulus Ω f a hΩ hf (hcl ha) hlocal
  obtain ⟨ξ, hξ⟩ := boundary_nonempty hΩ hb
  have : NeBot (𝓝[Ω] ξ) := mem_closure_iff_nhdsWithin_neBot.mp
    (frontier_subset_closure hξ)
  have hmem : ∀ᶠ w in 𝓝[Ω] ξ, w ∈ Ω := self_mem_nhdsWithin
  obtain ⟨w, hwΩ, hw⟩ :=
    (hmem.and (hlim ξ hξ (c - M) (sub_pos.mpr hMc))).exists
  have hw' : ‖f a‖ < c := by simpa [heq w hwΩ] using hw
  exact (not_lt_of_ge (hcz.le.trans hza)) hw'

/-- The maximum on the compact closure is attained on the boundary. -/
theorem exists_boundary_maximum :
    Specs.D12Complex.Ch06.BoundaryModulus.exists_boundary_maximum_type := by
  intro Ω f hΩ hb hf hc
  exact Complex.exists_mem_frontier_isMaxOn_norm hb hΩ.1
    ⟨fun z hz => (hf.2 z hz).differentiableWithinAt, hc⟩

theorem norm_le_boundary_maximum :
    Specs.D12Complex.Ch06.BoundaryModulus.norm_le_boundary_maximum_type := by
  intro Ω f hΩ hb hf hc z hz
  obtain ⟨ξ, hξ, hmax⟩ := exists_boundary_maximum Ω f hΩ hb hf hc
  have hbound : BddAbove ((fun w => ‖f w‖) '' frontier Ω) :=
    (hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure).bddAbove_image
      (hc.norm.mono frontier_subset_closure)
  exact (hmax hz).trans (le_csSup hbound (mem_image_of_mem _ hξ))

theorem maximum_closure_eq_boundary :
    Specs.D12Complex.Ch06.BoundaryModulus.maximum_closure_eq_boundary_type := by
  intro Ω f hΩ hb hf hc
  obtain ⟨ξ, hξ, hmax⟩ := exists_boundary_maximum Ω f hΩ hb hf hc
  have hcl : sSup ((fun w => ‖f w‖) '' closure Ω) = ‖f ξ‖ := by
    apply IsGreatest.csSup_eq
    exact ⟨mem_image_of_mem _ (frontier_subset_closure hξ), by
      rintro _ ⟨w, hw, rfl⟩
      exact hmax hw⟩
  have hfr : sSup ((fun w => ‖f w‖) '' frontier Ω) = ‖f ξ‖ := by
    apply IsGreatest.csSup_eq
    exact ⟨mem_image_of_mem _ hξ, by
      rintro _ ⟨w, hw, rfl⟩
      exact hmax (frontier_subset_closure hw)⟩
  exact hcl.trans hfr.symm

end D12Complex.BoundaryModulus
