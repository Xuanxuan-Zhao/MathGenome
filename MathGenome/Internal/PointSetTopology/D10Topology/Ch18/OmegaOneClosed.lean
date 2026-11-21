import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch18.OmegaOneClosed
import MathGenome.Internal.PointSetTopology.D10Topology.Ch18.OrdinalCompact
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.CountabilityConventions
import Mathlib.SetTheory.Cardinal.Regular

/-!
The closed first-uncountable ordinal interval, paper.tex d10:18:omega-one.
Every endpoint neighborhood meets the proper initial segment, but every
countable collection of points of that segment has a countable ordinal bound.
A tail above that bound excludes a sequence, and also defeats any countable
local base after choosing one initial-segment point in each base member.
-/

open Set Filter
open scoped Ordinal Topology
universe u
noncomputable section

namespace D10Topology.Ch18

abbrev OmegaOneInterval : Type (u + 1) := Specs.D10Topology.Ch18.OmegaOneClosed.ClosedInterval.{u}
abbrev omegaOneEndpoint : OmegaOneInterval.{u} :=
  Specs.D10Topology.Ch18.OmegaOneClosed.endpoint
abbrev omegaOneInitialSegment : Set OmegaOneInterval.{u} :=
  Specs.D10Topology.Ch18.OmegaOneClosed.initialSegment

local instance : TopologicalSpace OmegaOneInterval.{u} := Ch01.orderTopology _
local instance : OrderTopology OmegaOneInterval.{u} := ⟨rfl⟩

theorem omegaOne_orderTopology_eq_subspace :
    Ch01.orderTopology OmegaOneInterval.{u} =
      TopologicalSpace.induced (Subtype.val : OmegaOneInterval.{u} → Ordinal.{u})
        (Ch01.orderTopology Ordinal.{u}) :=
  ordinalInterval_orderTopology_eq_subspace ω₁

theorem omegaOne_compact_hausdorff :
    @Ch05.CoverCompact OmegaOneInterval.{u} (Ch01.orderTopology _) ∧
    @T2Space OmegaOneInterval.{u} (Ch01.orderTopology _) :=
  ordinalInterval_compact_hausdorff ω₁

/-- A countable family in the proper initial segment is bounded below ω₁. -/
theorem omegaOne_countable_bound {ι : Type*} [Countable ι]
    (a : ι → OmegaOneInterval.{u}) (ha : ∀ i, a i ∈ omegaOneInitialSegment) :
    ∃ b : OmegaOneInterval.{u}, b < omegaOneEndpoint ∧ ∀ i, a i ≤ b := by
  have hb : (⨆ i, (a i).val) < (ω₁ : Ordinal.{u}) :=
    Ordinal.iSup_lt_omega_one ha
  refine ⟨⟨⨆ i, (a i).val, zero_le, hb.le⟩, hb, ?_⟩
  intro i
  exact Ordinal.le_iSup (fun i => (a i).val) i

/-- No endpoint neighborhood is confined to the endpoint itself. -/
theorem omegaOne_endpoint_nhds_meets_initialSegment
    (U : Set OmegaOneInterval.{u}) (hU : U ∈ 𝓝 omegaOneEndpoint) :
    ∃ x ∈ U, x ∈ omegaOneInitialSegment := by
  have hzero : (0 : Ordinal.{u}) < ω₁ :=
    Ordinal.omega0_pos.trans Ordinal.omega0_lt_omega_one
  let z : OmegaOneInterval.{u} := ⟨0, le_rfl, hzero.le⟩
  obtain ⟨a, ha, hsub⟩ := exists_Ioc_subset_of_mem_nhds hU
    (⟨z, hzero⟩ : ∃ l : OmegaOneInterval.{u}, l < omegaOneEndpoint)
  have has : Order.succ a.val < (ω₁ : Ordinal.{u}) :=
    (Cardinal.isSuccLimit_omega 1).succ_lt ha
  let b : OmegaOneInterval.{u} := ⟨Order.succ a.val, zero_le, has.le⟩
  exact ⟨b, hsub ⟨Order.lt_succ a.val, has.le⟩, has⟩

theorem omegaOne_endpoint_mem_closure :
    omegaOneEndpoint ∈ closure omegaOneInitialSegment := by
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨x, hxU, hxY⟩ := omegaOne_endpoint_nhds_meets_initialSegment U hU
  exact ⟨x, hxU, hxY⟩

theorem omegaOne_no_sequence_tendsto_endpoint (a : ℕ → OmegaOneInterval.{u})
    (ha : ∀ n, a n ∈ omegaOneInitialSegment) :
    ¬ Tendsto a atTop (𝓝 omegaOneEndpoint) := by
  obtain ⟨b, hb, hab⟩ := omegaOne_countable_bound a ha
  intro h
  have ht : ∀ᶠ n in atTop, a n ∈ Ioi b := h (isOpen_Ioi.mem_nhds hb)
  obtain ⟨n, hn⟩ := ht.exists
  exact (not_lt_of_ge (hab n)) hn

theorem omegaOne_not_firstCountableAt_endpoint :
    ¬ Ch04.FirstCountableAt (Ch01.orderTopology OmegaOneInterval.{u}) omegaOneEndpoint := by
  classical
  rintro ⟨L, hLc, hL⟩
  have hex : ∀ V : L, ∃ x ∈ (V : Set OmegaOneInterval.{u}),
      x ∈ omegaOneInitialSegment := by
    intro V
    apply omegaOne_endpoint_nhds_meets_initialSegment
    exact (Ch01.neighborhood_iff_mem_nhds _ _ _).mp (hL.1 _ V.2)
  choose a haU haY using hex
  let : Countable L := hLc.to_subtype
  obtain ⟨b, hb, hab⟩ := omegaOne_countable_bound a haY
  have hN : Ch01.Neighborhood (Ch01.orderTopology _) omegaOneEndpoint (Ioi b) :=
    (Ch01.neighborhood_iff_mem_nhds _ _ _).mpr (isOpen_Ioi.mem_nhds hb)
  obtain ⟨V, hVL, hVN⟩ := hL.2 _ hN
  exact (not_lt_of_ge (hab ⟨V, hVL⟩)) (hVN (haU ⟨V, hVL⟩))

theorem omegaOne_not_firstCountable :
    ¬ Ch08.FirstCountable (Ch01.orderTopology OmegaOneInterval.{u}) := by
  intro h
  exact omegaOne_not_firstCountableAt_endpoint (h omegaOneEndpoint)

end D10Topology.Ch18
