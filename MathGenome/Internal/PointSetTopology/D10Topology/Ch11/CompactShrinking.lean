import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.CompactShrinking
import MathGenome.Internal.PointSetTopology.D10Topology.Ch11.LocalCompactConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.ShrinkingHierarchy

/-!
Shrinking in an LCH space (paper.tex, d10:11:compact-shrinking).

First upgrade the source's one compact neighborhood at each point to
Mathlib's arbitrarily small compact neighborhoods, using Hausdorffness.
The library's compact-set shrinking theorem then gives the required ambient
compact closures. The point statement is its singleton specialization, and
the source's regularity conclusion follows from the proved shrinking test.
The compact set and the ambient space are allowed to be empty.
-/

open Set
universe u

namespace D10Topology.Ch11

theorem locallyCompact_iff_locallyCompactSpace (X : Type u) [TopologicalSpace X]
    [T2Space X] : LocallyCompact X ↔ LocallyCompactSpace X := by
  constructor
  · intro h
    let : WeaklyLocallyCompactSpace X :=
      (locallyCompact_iff_weaklyLocallyCompactSpace X).mp h
    exact inferInstance
  · exact locallyCompact_of_mathlib_locallyCompactSpace X

theorem lch_iff_locallyCompactSpace_and_t2 (X : Type u) [TopologicalSpace X] :
    LCH X ↔ LocallyCompactSpace X ∧ T2Space X := by
  constructor
  · intro h
    let : T2Space X := h.2
    exact ⟨(locallyCompact_iff_locallyCompactSpace X).mp h.1, h.2⟩
  · rintro ⟨h, h2⟩
    exact ⟨locallyCompact_of_mathlib_locallyCompactSpace X h, h2⟩

theorem compact_set_shrinking {X : Type u} [TopologicalSpace X] (hX : LCH X)
    (C U : Set X) (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ V : Set X, IsOpen V ∧ C ⊆ V ∧ V ⊆ closure V ∧
      closure V ⊆ U ∧ IsCompact (closure V) := by
  let : T2Space X := hX.2
  let : WeaklyLocallyCompactSpace X :=
    (locallyCompact_iff_weaklyLocallyCompactSpace X).mp hX.1
  -- In a Hausdorff space both instances follow from weak local compactness;
  -- neither property is inserted into the source hypothesis.
  let : LocallyCompactSpace X :=
    (locallyCompact_iff_locallyCompactSpace X).mp hX.1
  let : RegularSpace X := inferInstance
  obtain ⟨V, hV, hCV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hC hU hCU
  exact ⟨V, hV, hCV, subset_closure, hVU, hVc⟩

theorem compact_shrinking {X : Type u} [TopologicalSpace X] (hX : LCH X)
    (x : X) (U : Set X) (hU : IsOpen U) (hx : x ∈ U) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ closure V ∧
      closure V ⊆ U ∧ IsCompact (closure V) := by
  simpa only [singleton_subset_iff] using
    compact_set_shrinking hX {x} U isCompact_singleton hU (singleton_subset_iff.mpr hx)

theorem lch_regular {X : Type u} [TopologicalSpace X] (hX : LCH X) :
    Ch07.Regular X := by
  apply (Ch07.regular_iff_shrinking X).mpr
  intro x U hU hx
  obtain ⟨V, hV, hxV, hVc, hVU, _⟩ := compact_shrinking hX x U hU hx
  exact ⟨V, hV, hxV, hVc, hVU⟩

end D10Topology.Ch11
