import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.LocalCompactConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.Compactness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch02.EmbeddingsAndCharacteristicMaps

/-!
The source conventions of Chapter 11. The independent Spec contains the
canonical predicates so downstream Specs can refer to the same objects.
In particular, `LocallyCompact` means just one compact neighborhood, and
`Proper` is not identified with Mathlib's `IsProperMap`.
The upgrade to arbitrarily small compact neighborhoods under Hausdorffness
is the separate compact-shrinking goal.
-/

open Set Topology
universe u v

namespace D10Topology.Ch11

abbrev LocallyCompact (X : Type u) [TopologicalSpace X] : Prop :=
  Specs.D10Topology.Ch11.LocalCompactConventions.LocallyCompact X

abbrev LCH (X : Type u) [TopologicalSpace X] : Prop :=
  Specs.D10Topology.Ch11.LocalCompactConventions.LCH X

abbrev Proper {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop := Specs.D10Topology.Ch11.LocalCompactConventions.Proper f

abbrev Perfect {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop := Specs.D10Topology.Ch11.LocalCompactConventions.Perfect f

abbrev HausdorffCompactification {X : Type u} {K : Type v}
    [TopologicalSpace X] [TopologicalSpace K] (i : X → K) : Prop :=
  Specs.D10Topology.Ch11.LocalCompactConventions.HausdorffCompactification i

abbrev SigmaCompact (X : Type u) [TopologicalSpace X] : Prop :=
  Specs.D10Topology.Ch11.LocalCompactConventions.SigmaCompact X

theorem locallyCompact_iff_compact_neighborhood (X : Type u) [TopologicalSpace X] :
    LocallyCompact X ↔ ∀ x : X, ∃ K : Set X, IsCompact K ∧ K ∈ 𝓝 x := by
  constructor
  · intro h x
    obtain ⟨K, hK, U, hU, hx, hUK⟩ := h x
    exact ⟨K, hK, mem_nhds_iff.mpr ⟨U, hUK, hU, hx⟩⟩
  · intro h x
    obtain ⟨K, hK, hxK⟩ := h x
    obtain ⟨U, hUK, hU, hx⟩ := mem_nhds_iff.mp hxK
    exact ⟨K, hK, U, hU, hx, hUK⟩

theorem locallyCompact_iff_weaklyLocallyCompactSpace (X : Type u) [TopologicalSpace X] :
    LocallyCompact X ↔ WeaklyLocallyCompactSpace X := by
  rw [locallyCompact_iff_compact_neighborhood]
  exact ⟨fun h => ⟨h⟩, fun h => h.exists_compact_mem_nhds⟩

theorem lch_iff_weaklyLocallyCompactSpace_and_t2 (X : Type u) [TopologicalSpace X] :
    LCH X ↔ WeaklyLocallyCompactSpace X ∧ T2Space X :=
  and_congr (locallyCompact_iff_weaklyLocallyCompactSpace X) Iff.rfl

theorem locallyCompact_of_mathlib_locallyCompactSpace (X : Type u) [TopologicalSpace X]
    (h : LocallyCompactSpace X) : LocallyCompact X := by
  let := h
  exact (locallyCompact_iff_weaklyLocallyCompactSpace X).mpr inferInstance

theorem hausdorffCompactification_iff_source {X : Type u} {K : Type v}
    [TopologicalSpace X] [TopologicalSpace K] (i : X → K) :
    HausdorffCompactification i ↔
      (∃ h : X ≃ₜ range i, ∀ x, (h x : K) = i x) ∧
      closure (range i) = univ ∧
      Specs.D10Topology.Ch05.Compactness.CoverCompact K ∧ T2Space K := by
  change (IsEmbedding i ∧ DenseRange i ∧ CompactSpace K ∧ T2Space K) ↔ _
  rw [Ch02.embedding_iff_homeomorph_range, denseRange_iff_closure_range,
    ← Ch05.coverCompact_iff_compactSpace]
  rfl

theorem sigmaCompact_iff_sequence (X : Type u) [TopologicalSpace X] :
    SigmaCompact X ↔ ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = univ := by
  constructor
  · rintro ⟨C, hcount, hc, hcover⟩
    have h := isSigmaCompact_sUnion_of_isCompact hcount hc
    rw [hcover] at h
    exact h
  · rintro ⟨K, hc, hcover⟩
    exact ⟨range K, countable_range K, by simpa only [forall_mem_range] using hc,
      by simpa only [sUnion_range] using hcover⟩

theorem sigmaCompact_iff_sigmaCompactSpace (X : Type u) [TopologicalSpace X] :
    SigmaCompact X ↔ SigmaCompactSpace X :=
  (sigmaCompact_iff_sequence X).trans SigmaCompactSpace_iff_exists_compact_covering.symm

theorem empty_locallyCompact (X : Type u) [TopologicalSpace X] [IsEmpty X] :
    LocallyCompact X := fun x => isEmptyElim x

theorem empty_lch (X : Type u) [TopologicalSpace X] [IsEmpty X] : LCH X :=
  ⟨empty_locallyCompact X, inferInstance⟩

theorem empty_sigmaCompact (X : Type u) [TopologicalSpace X] [IsEmpty X] :
    SigmaCompact X := by
  refine ⟨∅, countable_empty, ?_, ?_⟩
  · simp
  · ext x
    exact isEmptyElim x

theorem identity_hausdorffCompactification (X : Type u) [TopologicalSpace X]
    [CompactSpace X] [T2Space X] : HausdorffCompactification (id : X → X) :=
  ⟨IsEmbedding.id, denseRange_id, inferInstance, inferInstance⟩

theorem empty_identity_hausdorffCompactification (X : Type u) [TopologicalSpace X]
    [IsEmpty X] : HausdorffCompactification (id : X → X) :=
  identity_hausdorffCompactification X

end D10Topology.Ch11
