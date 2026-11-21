import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsNormability
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.BalancedBounded
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06GaugeProperties

/-! Normability of a Hausdorff real or complex locally convex space.
The singleton seminorm family below is positive definite, and therefore
is a norm, not merely a seminorm inducing a nonseparated topology. -/

open Set Filter
open scoped Topology

namespace ExpandedFA.P1

theorem bounded_neighborhood_gauge_norm : TvsNormabilitySpec.GaugeNorm := by
  intro 𝕜 E _ _ _ _ _ _ _ hE U hU hUb
  let : IsTopologicalAddGroup E := hE.1.1
  let : ContinuousSMul 𝕜 E := hE.1.2
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  obtain ⟨V, hV, ho, hb, hc, hVU⟩ :=
    absolutely_convex_neighborhood_basis 𝕜 E hE.2 U hU
  have hVb : Bounded V := by
    intro W hW
    obtain ⟨s, hs, hscale⟩ := hUb W hW
    exact ⟨s, hs, fun t ht => hVU.trans (hscale t ht)⟩
  have hVB : Bornology.IsVonNBounded ℝ V := (bounded_iff_isVonNBounded V).mp hVb
  have h0 : (0 : E) ∈ V := mem_of_mem_nhds hV
  obtain ⟨⟨p, hp, hcont⟩, _⟩ :=
    C06.minkowskiGauge_continuous_seminorm V hc h0 ho hb
  have hpg : (p : E → ℝ) = gauge V := funext hp
  have hpos : ∀ x, p x = 0 ↔ x = 0 := by
    intro x
    rw [hpg]
    exact gauge_eq_zero (absorbent_nhds_zero hV) hVB
  have htop : WithSeminorms (fun _ : Unit => p) := by
    rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf, iInf_const, hpg]
    exact (comap_gauge_nhds_zero hVB hV).symm
  exact ⟨V, hV, ho, hb, hc, hVU, hVb, p, hp, hcont, hpos, htop⟩

theorem normable_iff_bounded_neighborhood : TvsNormabilitySpec.Normability := by
  intro 𝕜 E _ _ _ _ _ _ _ hE
  let : IsTopologicalAddGroup E := hE.1.1
  let : ContinuousSMul 𝕜 E := hE.1.2
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  constructor
  · rintro ⟨p, _hpos, hp⟩
    have hpR : WithSeminorms (fun _ : Unit => p.restrictScalars ℝ) := by
      rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf] at hp ⊢
      exact hp
    refine ⟨p.ball 0 1, Seminorm.ball_mem_nhds (hp.continuous_seminorm ()) one_pos, ?_⟩
    apply (bounded_iff_isVonNBounded _).mpr
    apply hpR.isVonNBounded_iff_seminorm_bounded.mpr
    intro i
    exact ⟨1, one_pos, fun x hx => p.mem_ball_zero.mp hx⟩
  · rintro ⟨U, hU, hUb⟩
    obtain ⟨V, _, _, _, _, _, _, p, _, _, hpos, htop⟩ :=
      bounded_neighborhood_gauge_norm 𝕜 E hE U hU hUb
    exact ⟨p, hpos, htop⟩

end ExpandedFA.P1
