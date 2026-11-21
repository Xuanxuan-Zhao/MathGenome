import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.QuotientRestrictionCounterexample
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.QuotientMaps
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.Subspaces
import Mathlib.Topology.Algebra.Group.ContinuousDiv

/-!
The explicit interval example of paper.tex, d10:03:restriction-failure.
Closedness is checked on the two summands, using closed real intervals
and translation. All data (including the usual topologies) are defined
independently in the specification.
-/

open Set Topology

namespace D10Topology.Ch03.QuotientRestrictionCounterexample
open RestrictionExampleData

theorem q_continuous : Continuous q := by
  apply Continuous.sumElim
  · exact continuous_subtype_val.subtype_mk _
  · exact (continuous_subtype_val.sub continuous_const).subtype_mk _

theorem q_closed : IsClosedMap q := by
  apply IsClosedMap.sumElim
  · exact isClosed_Icc.isClosedMap_subtype_val.subtype_mk _
  · exact ((Homeomorph.subRight (1 : ℝ)).isClosedMap.comp
      isClosed_Icc.isClosedMap_subtype_val).subtype_mk _

theorem q_surjective : Function.Surjective q := by
  intro y
  by_cases h : y.val ≤ 1
  · exact ⟨Sum.inl ⟨y.val, y.property.1, h⟩, Subtype.ext rfl⟩
  · refine ⟨Sum.inr ⟨y.val + 1, ?_⟩, ?_⟩
    · constructor <;> linarith [y.property.2]
    · apply Subtype.ext
      change y.val + 1 - 1 = y.val
      ring

theorem q_quotient : QuotientMap q :=
  continuous_closed_surjection_quotient q q_continuous q_closed q_surjective

theorem restriction_continuous : Continuous restricted :=
  q_continuous.comp continuous_subtype_val

theorem restriction_surjective : Function.Surjective restricted := by
  intro y
  by_cases h : y.val < 1
  · exact ⟨⟨Sum.inl ⟨y.val, y.property.1, h.le⟩, h⟩, Subtype.ext rfl⟩
  · refine ⟨⟨Sum.inr ⟨y.val + 1, ?_⟩, trivial⟩, ?_⟩
    · constructor <;> linarith [y.property.2]
    · apply Subtype.ext
      change y.val + 1 - 1 = y.val
      ring

theorem witness_preimage : restricted ⁻¹' V = secondSummand := by
  ext a
  obtain ⟨x, hx⟩ := a
  cases x with
  | inl t =>
    change (1 ≤ t.val) ↔ Sum.inl t ∈ range (Sum.inr : Right → X)
    have ht : t.val < 1 := hx
    simp only [mem_range, Sum.inr_ne_inl, exists_false, iff_false]
    exact not_le.mpr ht
  | inr t =>
    change (1 ≤ t.val - 1) ↔ Sum.inr t ∈ range (Sum.inr : Right → X)
    constructor
    · intro _
      exact ⟨t, rfl⟩
    · intro _
      linarith [t.property.1]

theorem witness_preimage_open : IsOpen (restricted ⁻¹' V) := by
  rw [witness_preimage]
  exact isOpen_range_inr.preimage continuous_subtype_val

theorem witness_not_open : ¬ IsOpen V := by
  intro ho
  have hone : one ∈ V := by norm_num [one, V]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ho one hone
  let δ : ℝ := min ε 1 / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ < ε := by
    have := min_le_left ε 1
    dsimp [δ]
    linarith
  have hδ1 : δ ≤ 1 / 2 := by
    have := min_le_right ε 1
    dsimp [δ]
    linarith
  let y : Y := ⟨1 - δ, by constructor <;> linarith⟩
  have hyball : y ∈ Metric.ball one ε := by
    change dist (1 - δ) (1 : ℝ) < ε
    rw [Real.dist_eq, abs_of_nonpos (by linarith)]
    linarith
  have hy := hball hyball
  change 1 ≤ 1 - δ at hy
  linarith

theorem restriction_not_quotient : ¬ QuotientMap restricted := by
  intro h
  exact witness_not_open ((h.2 V).mpr witness_preimage_open)

theorem fiber_witness :
    retained ∈ A ∧ discarded ∉ A ∧ retained ≠ discarded ∧
      q retained = one ∧ q discarded = one := by
  refine ⟨trivial, ?_, Sum.inr_ne_inl, ?_, ?_⟩
  · norm_num [discarded, A]
  · apply Subtype.ext
    norm_num [q, retained, rightMap, one]
  · rfl

theorem fiber_one : q ⁻¹' {one} = {discarded, retained} := by
  ext x
  cases x with
  | inl t =>
    simp only [mem_preimage, mem_singleton_iff, mem_insert_iff]
    constructor
    · intro h
      left
      congr 1
      apply Subtype.ext
      have hv := congrArg (fun y : Y => y.val) h
      exact hv
    · rintro (h | h)
      · simpa only [h] using fiber_witness.2.2.2.2
      · exact (Sum.inl_ne_inr h).elim
  | inr t =>
    simp only [mem_preimage, mem_singleton_iff, mem_insert_iff]
    constructor
    · intro h
      right
      congr 1
      apply Subtype.ext
      have hv := congrArg Subtype.val h
      change t.val - 1 = 1 at hv
      change t.val = 2
      linarith
    · rintro (h | h)
      · exact (Sum.inr_ne_inl h).elim
      · simpa only [h] using fiber_witness.2.2.2.1

theorem restricted_fiber_one :
    restricted ⁻¹' {one} = {⟨retained, trivial⟩} := by
  ext a
  constructor
  · intro h
    have hx : a.val ∈ q ⁻¹' {one} := h
    rw [fiber_one] at hx
    rcases hx with hdiscarded | hretained
    · exact (fiber_witness.2.1 (hdiscarded ▸ a.property)).elim
    · exact Subtype.ext hretained
  · intro h
    have ha : a = ⟨retained, trivial⟩ := h
    rw [ha]
    exact fiber_witness.2.2.2.1

theorem A_not_saturated : ¬ Saturated q A := by
  intro h
  have hf := (saturated_iff_fiberwise q A).mp h
  exact fiber_witness.2.1
    (hf retained fiber_witness.1 discarded
      (fiber_witness.2.2.2.2.trans fiber_witness.2.2.2.1.symm))

end D10Topology.Ch03.QuotientRestrictionCounterexample
