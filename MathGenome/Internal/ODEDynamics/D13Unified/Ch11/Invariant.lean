import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Invariant
import MathGenome.Internal.ODEDynamics.D13Unified.Ch03.DerivativeCriterion
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.CompactEscape

/-! Compact invariant subsets of the open state domain support complete
solutions. The argument excludes finite maximal endpoints by compact escape
from the time-state cylinders over the invariant set. -/
noncomputable section
open Set

namespace D13Unified.Ch11.Invariant
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch04.MaximalSolutionMap
open Specs.D13Unified.Ch11.Invariant
open Ch06.StateDerivative
universe u

/-- Positive invariance on the actual lifespan, relative to Ω. -/
def IsPositivelyInvariant : positiveInvariantType := positiveInvariantValue

/-- Invariance for both signs of time on the actual lifespan, relative to Ω. -/
def IsInvariant : invariantType := invariantValue

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Compact forward confinement excludes a finite right endpoint. -/
lemma upperEndpoint_eq_top (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) (S : Set E) (hS : IsCompact S)
    (hInv : IsPositivelyInvariant F S) {x : E} (hx : x ∈ S) :
    upperEndpointValue F.toODE 0 x = ⊤ := by
  have hL := F.locallyLipschitzInState_of_contDiffOn hF
  obtain ⟨hsol, hz, hi, hm, hend, hc, hu⟩ :=
    ODE.canonical_solution F.toODE hL 0 x (hInv.1 hx)
  change lowerEndpointValue F.toODE 0 x < (0 : ℝ) ∧
    (0 : ℝ) < upperEndpointValue F.toODE 0 x ∧
    (maximalIntervalValue F.toODE 0 x).carrier =
      {t : ℝ | lowerEndpointValue F.toODE 0 x < (t : EReal) ∧
        (t : EReal) < upperEndpointValue F.toODE 0 x} at hend
  cases hb : upperEndpointValue F.toODE 0 x using EReal.rec with
  | bot => simpa [hb] using hend.2.1
  | top => rfl
  | coe b =>
    exfalso
    have h0b : (0 : ℝ) < b := by simpa [hb] using hend.2.1
    obtain ⟨τ, hτ, hesc⟩ := Ch04.CompactEscape.right_escape F.toODE hL 0 x
      (hInv.1 hx) b hb (Icc 0 b ×ˢ S) (isCompact_Icc.prod hS)
      (fun q hq => hInv.1 hq.2)
    let t : ℝ := (max τ 0 + b) / 2
    have hmb : max τ 0 < b := max_lt hτ h0b
    have hmt : max τ 0 < t := by dsimp [t]; linarith
    have htb : t < b := by dsimp [t]; linarith
    have ht0 : 0 ≤ t := (le_max_right τ 0).trans hmt.le
    have htI : t ∈ (flowInterval F x).carrier := by
      change t ∈ (maximalIntervalValue F.toODE 0 x).carrier
      rw [hend.2.2]
      exact ⟨hend.1.trans_le (EReal.coe_le_coe ht0), by simpa [hb] using htb⟩
    have heval := (ODE.solutionValue_on_domain F.toODE hL t 0 x
      ⟨hInv.1 hx, htI⟩).1
    apply hesc t ⟨(le_max_left τ 0).trans_lt hmt, htb⟩
    refine ⟨⟨ht0, htb.le⟩, ?_⟩
    rw [heval]
    exact hInv.2 x hx t htI ht0

/-- Forward completeness is deduced after positive invariance is defined. -/
theorem compact_forward_complete : CompactForwardCompleteness.{u} := by
  intro E _ _ _ F hF S hS hInv x hx
  have hL := F.locallyLipschitzInState_of_contDiffOn hF
  obtain ⟨hsol, hz, hi, hm, hend, hc, hu⟩ :=
    ODE.canonical_solution F.toODE hL 0 x (hInv.1 hx)
  change lowerEndpointValue F.toODE 0 x < (0 : ℝ) ∧
    (0 : ℝ) < upperEndpointValue F.toODE 0 x ∧
    (maximalIntervalValue F.toODE 0 x).carrier =
      {t : ℝ | lowerEndpointValue F.toODE 0 x < (t : EReal) ∧
        (t : EReal) < upperEndpointValue F.toODE 0 x} at hend
  have hb := upperEndpoint_eq_top F hF S hS hInv hx
  have hdom : Ici (0 : ℝ) ⊆ (flowInterval F x).carrier := by
    intro t ht
    change t ∈ (maximalIntervalValue F.toODE 0 x).carrier
    rw [hend.2.2]
    exact ⟨hend.1.trans_le (EReal.coe_le_coe ht), by simp [hb]⟩
  exact ⟨hdom, fun t ht => hInv.2 x hx t (hdom ht) ht⟩

/-- Two-sided compact confinement excludes a finite left endpoint as well. -/
lemma lowerEndpoint_eq_bot (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) (S : Set E) (hS : IsCompact S)
    (hInv : IsInvariant F S) {x : E} (hx : x ∈ S) :
    lowerEndpointValue F.toODE 0 x = ⊥ := by
  have hL := F.locallyLipschitzInState_of_contDiffOn hF
  obtain ⟨hsol, hz, hi, hm, hend, hc, hu⟩ :=
    ODE.canonical_solution F.toODE hL 0 x (hInv.1 hx)
  change lowerEndpointValue F.toODE 0 x < (0 : ℝ) ∧
    (0 : ℝ) < upperEndpointValue F.toODE 0 x ∧
    (maximalIntervalValue F.toODE 0 x).carrier =
      {t : ℝ | lowerEndpointValue F.toODE 0 x < (t : EReal) ∧
        (t : EReal) < upperEndpointValue F.toODE 0 x} at hend
  cases ha : lowerEndpointValue F.toODE 0 x using EReal.rec with
  | bot => rfl
  | top => simpa [ha] using hend.1
  | coe a =>
    exfalso
    have ha0 : a < (0 : ℝ) := by simpa [ha] using hend.1
    obtain ⟨τ, hτ, hesc⟩ := Ch04.CompactEscape.left_escape F.toODE hL 0 x
      (hInv.1 hx) a ha (Icc a 0 ×ˢ S) (isCompact_Icc.prod hS)
      (fun q hq => hInv.1 hq.2)
    let t : ℝ := (a + min τ 0) / 2
    have ham : a < min τ 0 := lt_min hτ ha0
    have htm : t < min τ 0 := by dsimp [t]; linarith
    have hat : a < t := by dsimp [t]; linarith
    have ht0 : t ≤ 0 := htm.le.trans (min_le_right τ 0)
    have htI : t ∈ (flowInterval F x).carrier := by
      change t ∈ (maximalIntervalValue F.toODE 0 x).carrier
      rw [hend.2.2]
      exact ⟨by simpa [ha] using hat, (EReal.coe_le_coe ht0).trans_lt hend.2.1⟩
    have heval := (ODE.solutionValue_on_domain F.toODE hL t 0 x
      ⟨hInv.1 hx, htI⟩).1
    apply hesc t ⟨hat, htm.trans_le (min_le_left τ 0)⟩
    refine ⟨⟨hat.le, ht0⟩, ?_⟩
    rw [heval]
    exact hInv.2 x hx t htI

/-- The entire canonical maximal interval is ℝ and its orbit stays in S. -/
theorem compact_complete : CompactCompleteness.{u} := by
  intro E _ _ _ F hF S hS hInv x hx
  have hL := F.locallyLipschitzInState_of_contDiffOn hF
  obtain ⟨hsol, hz, hi, hm, hend, hc, hu⟩ :=
    ODE.canonical_solution F.toODE hL 0 x (hInv.1 hx)
  change lowerEndpointValue F.toODE 0 x < (0 : ℝ) ∧
    (0 : ℝ) < upperEndpointValue F.toODE 0 x ∧
    (maximalIntervalValue F.toODE 0 x).carrier =
      {t : ℝ | lowerEndpointValue F.toODE 0 x < (t : EReal) ∧
        (t : EReal) < upperEndpointValue F.toODE 0 x} at hend
  have ha := lowerEndpoint_eq_bot F hF S hS hInv hx
  have hb := upperEndpoint_eq_top F hF S hS
    ⟨hInv.1, fun y hy t ht _ => hInv.2 y hy t ht⟩ hx
  have hdom : (flowInterval F x).carrier = univ := by
    change (maximalIntervalValue F.toODE 0 x).carrier = univ
    rw [hend.2.2]
    simp [ha, hb]
  exact ⟨hdom, fun t => hInv.2 x hx t (hdom.symm ▸ mem_univ t)⟩

end D13Unified.Ch11.Invariant
