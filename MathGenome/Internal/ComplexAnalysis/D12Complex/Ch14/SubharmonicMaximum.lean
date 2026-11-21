import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.SubharmonicMaximum
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.SubharmonicDefinition
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.BoundaryMaximum
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic.Linarith

noncomputable section
open Set Metric
open scoped Topology

namespace D12Complex.SubharmonicMaximum

/-- Submean inequalities force the maximum set to be open. Together with
compact strict superlevels supplied by the boundary limit, this excludes
any value above the boundary bound, without a boundary extension. -/
theorem subharmonic_boundary_maximum :
    Specs.D12Complex.Ch14.SubharmonicMaximum.subharmonic_boundary_maximum_type := by
  intro U u M hUb hu hb z hz
  have hm := SubharmonicDefinition.subharmonicOn_circleSubmeanOn hu
  by_contra hn
  have hzt : M < u z := lt_of_not_ge hn
  obtain ⟨a, ha, hmax⟩ :=
    (BoundaryMaximum.isCompact_superlevel hu.1 hUb hu.2.1 hb hzt).exists_isMaxOn
      ⟨z, hz, le_rfl⟩ (hu.2.1.mono (fun w hw => hw.1))
  have hglobal : ∀ w ∈ U, u w ≤ u a := by
    intro w hw
    by_cases ht : u z ≤ u w
    · exact hmax ⟨hw, ht⟩
    · exact (le_of_not_ge ht).trans ha.2
  let K : Set ℂ := {w ∈ U | u a ≤ u w}
  have hKc : IsCompact K :=
    BoundaryMaximum.isCompact_superlevel hu.1 hUb hu.2.1 hb (hzt.trans_le ha.2)
  have hKo : IsOpen K := by
    apply isOpen_iff_mem_nhds.mpr
    intro w hw
    obtain ⟨ρ, hρ, hsub, heq⟩ :=
      SubharmonicDefinition.submean_maximum_locally_constant hu.1 hu.2.1 hm.2.2 hw.1
        (fun v hv => (hglobal v hv).trans hw.2)
    apply Filter.mem_of_superset (ball_mem_nhds w hρ)
    intro v hv
    exact ⟨hsub hv, hw.2.trans_eq (heq v hv).symm⟩
  have heq : K = univ := (show IsClopen K from ⟨hKc.isClosed, hKo⟩).eq_univ
    ⟨a, ha.1, le_rfl⟩
  exact NormedSpace.unbounded_univ ℝ ℂ (heq ▸ hKc.isBounded)

/-- Equality in the submean upper bound gives local constancy at each
maximum point. The maximum set is then relatively clopen in the domain. -/
theorem subharmonic_strong_maximum :
    Specs.D12Complex.Ch14.SubharmonicMaximum.subharmonic_strong_maximum_type := by
  intro U u hU hu a ha hmax
  have hm := SubharmonicDefinition.subharmonicOn_circleSubmeanOn hu
  let V : Set ℂ := U ∩ {z | u z = u a}
  let W : Set ℂ := U ∩ {z | u z ≠ u a}
  have hVo : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    obtain ⟨ρ, hρ, hsub, heq⟩ :=
      SubharmonicDefinition.submean_maximum_locally_constant hu.1 hu.2.1 hm.2.2 hz.1
        (fun w hw => (hmax w hw).trans_eq hz.2.symm)
    apply Filter.mem_of_superset (ball_mem_nhds z hρ)
    intro w hw
    exact ⟨hsub hw, (heq w hw).trans hz.2⟩
  have hWo : IsOpen W := hu.2.1.isOpen_inter_preimage hu.1 isOpen_ne
  have hVW : Disjoint V W := disjoint_left.mpr (fun _ hv hw => hw.2 hv.2)
  have hcover : U ⊆ V ∪ W := by
    intro z hz
    rcases eq_or_ne (u z) (u a) with h | h
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩
  have hsub := hU.2.2.subset_left_of_subset_union hVo hWo hVW hcover
    (show (U ∩ V).Nonempty from ⟨a, ha, ha, rfl⟩)
  exact fun z hz => (hsub hz).2

/-- Circle averages are linear and a harmonic function has its center
value as its circle average. Thus subtraction preserves the submean
inequality, hence the original Poisson-comparison definition. -/
theorem subharmonic_sub_harmonic :
    Specs.D12Complex.Ch14.SubharmonicMaximum.subharmonic_sub_harmonic_type := by
  intro U u h hu hh
  apply (SubharmonicDefinition.subharmonicOn_iff_circleSubmeanOn U _).mpr
  have hm := SubharmonicDefinition.subharmonicOn_circleSubmeanOn hu
  refine ⟨hu.1, hu.2.1.sub hh.2.1.continuousOn, ?_⟩
  intro a R hR hsub
  have hs : sphere a R ⊆ U := sphere_subset_closedBall.trans hsub
  have hui := (hu.2.1.mono hs).circleIntegrable hR.le
  have hhi := (hh.2.1.continuousOn.mono hs).circleIntegrable hR.le
  rw [Real.circleAverage_fun_sub hui hhi,
    MeanValueStrongPrinciple.circle_average_eq hh hR.le hsub]
  exact sub_le_sub_right (hm.2.2 a R hR hsub) (h a)

theorem subharmonic_harmonic_boundary_comparison :
    Specs.D12Complex.Ch14.SubharmonicMaximum.subharmonic_harmonic_boundary_comparison_type := by
  intro U u h M hUb hu hh hb z hz
  have hle := subharmonic_boundary_maximum U (fun w => u w - h w) M hUb
    (subharmonic_sub_harmonic U u h hu hh) hb z hz
  linarith

theorem subharmonic_harmonic_comparison :
    Specs.D12Complex.Ch14.SubharmonicMaximum.subharmonic_harmonic_comparison_type := by
  intro U u h hUb hu hh hb z hz
  simpa using subharmonic_harmonic_boundary_comparison U u h 0 hUb hu hh hb z hz

end D12Complex.SubharmonicMaximum
