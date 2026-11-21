import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch04.CompactConfinement
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.CompactEscape

noncomputable section
open Set
open Specs.D13Unified.Ch04.MaximalSolutionMap
open Specs.D13Unified.Ch04.CompactConfinement

namespace D13Unified.Ch04.CompactConfinement
universe u

/-- A time-dependent family of compact state sets, with the prescribed product
containment in the original domain, rules out a finite maximal right endpoint. -/
theorem compact_confinement : compactConfinementExpected.{u} := by
  intro E _ _ _ F hF s ξ hs hconf
  obtain ⟨hx, hsi, hξ, hmax, hend, _⟩ := ODE.canonical_solution F hF s ξ hs
  by_contra htop
  have hbot : upperEndpointValue F s ξ ≠ ⊥ := ne_bot_of_gt hend.2.1
  lift upperEndpointValue F s ξ to ℝ using ⟨htop, hbot⟩ with b hb
  have hsb : s < b := EReal.coe_lt_coe_iff.mp (hb ▸ hend.2.1)
  obtain ⟨K, hK, hKU, hvalues⟩ := hconf (b + 1) (by linarith)
  obtain ⟨τ, hτ, hescape⟩ := CompactEscape.right_escape F hF s ξ hs b hb.symm
    (Icc s b ×ˢ K) (isCompact_Icc.prod hK) (by
      intro p hp
      exact hKU ⟨⟨hp.1.1, by linarith [hp.1.2]⟩, hp.2⟩)
  obtain ⟨t, htlo, htb⟩ := exists_between (max_lt hτ hsb)
  have hst : s < t := (le_max_right τ s).trans_lt htlo
  have htI : t ∈ (maximalIntervalValue F s ξ).carrier := by
    change t ∈ (maximalDataValue F s ξ).interval.carrier
    rw [hend.2.2]
    refine ⟨hend.1.trans (EReal.coe_lt_coe_iff.mpr hst), ?_⟩
    change (t : EReal) < upperEndpointValue F s ξ
    rw [← hb]
    exact EReal.coe_lt_coe_iff.mpr htb
  exact hescape t ⟨(le_max_left τ s).trans_lt htlo, htb⟩
    ⟨⟨hst.le, htb.le⟩, hvalues t htI ⟨hst.le, by linarith⟩⟩

end D13Unified.Ch04.CompactConfinement
