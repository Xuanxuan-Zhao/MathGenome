import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch02.ClosedPastingCounterexample
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.NormNum

/-! A countable closed cover whose restrictions paste to a discontinuous map.
The singleton pieces are indexed by the points of the countable space itself;
therefore there are no repeated nonempty pieces. -/

open Set Filter
open scoped Topology

namespace D10Topology.Ch02.ClosedPastingCounterexample

abbrev carrier := Specs.D10Topology.Ch02.ClosedPastingCounterexample.carrier
abbrev Space := Specs.D10Topology.Ch02.ClosedPastingCounterexample.Space
abbrev origin : Space := Specs.D10Topology.Ch02.ClosedPastingCounterexample.origin
noncomputable abbrev term := Specs.D10Topology.Ch02.ClosedPastingCounterexample.term
noncomputable abbrev stepMap := Specs.D10Topology.Ch02.ClosedPastingCounterexample.stepMap
abbrev pieces := Specs.D10Topology.Ch02.ClosedPastingCounterexample.pieces

theorem countable_space : Countable Space := by
  apply Set.Countable.to_subtype
  apply ((countable_singleton (0 : ℝ)).union
    (countable_range (fun n : ℕ => 1 / (n : ℝ)))).mono
  rintro x (hx | ⟨n, _, rfl⟩)
  · exact Or.inl hx
  · exact Or.inr ⟨n, rfl⟩

theorem singleton_closed_cover :
    (∀ x : Space, IsClosed (pieces x)) ∧ (⋃ x : Space, pieces x) = univ := by
  refine ⟨fun _ => isClosed_singleton, ?_⟩
  ext x
  simp [pieces, Specs.D10Topology.Ch02.ClosedPastingCounterexample.pieces]

theorem restrictions_continuous (x : Space) :
    Continuous (fun a : pieces x => stepMap a.val) := by
  have heq : (fun a : pieces x => stepMap a.val) = fun _ => stepMap x := by
    funext a
    have h : a.val = x := a.property
    rw [h]
  rw [heq]
  exact continuous_const

theorem map_values :
    stepMap origin = 0 ∧ ∀ (n : ℕ) (hn : 1 ≤ n),
      stepMap ⟨1 / (n : ℝ), Or.inr ⟨n, hn, rfl⟩⟩ = 1 := by
  refine ⟨by simp [stepMap, Specs.D10Topology.Ch02.ClosedPastingCounterexample.stepMap,
    origin, Specs.D10Topology.Ch02.ClosedPastingCounterexample.origin], ?_⟩
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  simp [stepMap, Specs.D10Topology.Ch02.ClosedPastingCounterexample.stepMap, hn0]

theorem interval_preimage :
    stepMap ⁻¹' Ioo (-(1 / 2 : ℝ)) (1 / 2) = {origin} := by
  ext x
  have hx : x = origin ↔ x.val = 0 := by
    constructor
    · rintro rfl; rfl
    · exact fun h => Subtype.ext h
  simp only [mem_preimage, mem_Ioo, mem_singleton_iff, hx]
  by_cases h : x.val = 0 <;>
    norm_num [stepMap, Specs.D10Topology.Ch02.ClosedPastingCounterexample.stepMap, h]

/-- Positive reciprocal points never equal zero. -/
theorem term_ne_origin (n : ℕ) : term n ≠ origin := by
  intro h
  have hz : 1 / ((n : ℝ) + 1) = 0 := congrArg Subtype.val h
  exact (one_div_ne_zero (by positivity : (n : ℝ) + 1 ≠ 0)) hz

theorem term_injective : Function.Injective term := by
  intro m n h
  have hval : 1 / ((m : ℝ) + 1) = 1 / ((n : ℝ) + 1) := congrArg Subtype.val h
  have hmn : (m : ℝ) + 1 = (n : ℝ) + 1 := inv_injective (by simpa only [one_div] using hval)
  exact Nat.cast_injective (add_right_cancel hmn)

theorem term_tendsto : Tendsto term atTop (𝓝 origin) := by
  apply tendsto_subtype_rng.mpr
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- Every neighborhood of zero contains an infinite tail of distinct points. -/
theorem neighborhood_infinite (N : Set Space) (hN : N ∈ 𝓝 origin) : N.Infinite := by
  have hevent : ∀ᶠ n in atTop, term n ∈ N := term_tendsto.eventually hN
  obtain ⟨M, hM⟩ := eventually_atTop.mp hevent
  intro hfin
  have hpre : (term ⁻¹' N).Finite := hfin.preimage term_injective.injOn
  exact Set.Ici_infinite M (hpre.subset hM)

theorem origin_not_open : ¬ IsOpen ({origin} : Set Space) := by
  intro hopen
  exact neighborhood_infinite {origin} (hopen.mem_nhds (mem_singleton origin))
    (finite_singleton origin)

theorem map_not_continuous_at_origin : ¬ ContinuousAt stepMap origin := by
  intro h
  have hI : Ioo (-(1 / 2 : ℝ)) (1 / 2) ∈ 𝓝 (stepMap origin) := by
    rw [map_values.1]
    exact isOpen_Ioo.mem_nhds (by norm_num)
  have hN := h.preimage_mem_nhds hI
  rw [interval_preimage] at hN
  exact neighborhood_infinite {origin} hN (finite_singleton origin)

theorem map_not_continuous : ¬ Continuous stepMap := by
  intro h
  apply origin_not_open
  rw [← interval_preimage]
  exact isOpen_Ioo.preimage h

theorem not_locally_finite_at_origin (N : Set Space) (hN : N ∈ 𝓝 origin) :
    {x : Space | (pieces x ∩ N).Nonempty}.Infinite := by
  have heq : {x : Space | (pieces x ∩ N).Nonempty} = N := by
    ext x
    simp [pieces, Specs.D10Topology.Ch02.ClosedPastingCounterexample.pieces]
  rw [heq]
  exact neighborhood_infinite N hN

theorem cover_not_locally_finite : ¬ LocallyFinite pieces := by
  intro h
  obtain ⟨N, hN, hfinite⟩ := h origin
  exact not_locally_finite_at_origin N hN hfinite

end D10Topology.Ch02.ClosedPastingCounterexample
