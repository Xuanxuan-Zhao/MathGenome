import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.CompactImagesAndSeparation
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.Compactness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch02.EmbeddingsAndCharacteristicMaps
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.QuotientMaps
import Mathlib.Topology.Order.Compact

/-!
Continuous images, elementary compact separation, real extrema, and the
compact-to-Hausdorff test. The separation proof uses compact induction
(finite union of local separating neighborhoods), before the extreme-value
argument. None of these proofs uses product compactness.
-/

open Set Topology
universe u v

namespace D10Topology.Ch05

section Images
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

theorem continuous_image_compact_subset (f : X → Y) (K : Set X)
    (hK : SubspaceCompact K) (hf : Continuous f) : SubspaceCompact (f '' K) :=
  (subspaceCompact_iff_isCompact _).mpr
    (((subspaceCompact_iff_isCompact K).mp hK).image hf)

theorem continuous_compact_image (f : X → Y) (hX : CoverCompact X)
    (hf : Continuous f) : SubspaceCompact (range f) := by
  apply (subspaceCompact_iff_isCompact _).mpr
  simpa only [image_univ] using ((coverCompact_iff_isCompact_univ X).mp hX).image hf

end Images

section Separation
variable {X : Type u} [TopologicalSpace X]

/-- Finite unions of local separating neighborhoods separate a compact set.
The empty compact set uses the empty open neighborhood. -/
theorem compact_separation_of_pointwise {A B : Set X} (hA : IsCompact A)
    (h : ∀ a ∈ A, SeparatedNhds ({a} : Set X) B) : SeparatedNhds A B := by
  apply hA.induction_on (p := fun C => SeparatedNhds C B)
    (SeparatedNhds.empty_left B)
    (fun _ _ hst hsep => hsep.mono hst Subset.rfl)
    (fun _ _ hs ht => hs.union_left ht)
  intro a ha
  obtain ⟨U, V, hU, hV, haU, hBV, hd⟩ := h a ha
  exact ⟨U, mem_nhdsWithin_of_mem_nhds (hU.mem_nhds (haU (mem_singleton a))),
    U, V, hU, hV, Subset.rfl, hBV, hd⟩

variable [T2Space X]

theorem compact_point_separation (K : Set X) (hK : SubspaceCompact K)
    (x : X) (hx : x ∉ K) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ K ⊆ V ∧ Disjoint U V := by
  have hsep : SeparatedNhds K ({x} : Set X) :=
    compact_separation_of_pointwise ((subspaceCompact_iff_isCompact K).mp hK) (by
      intro y hy
      have hne : y ≠ x := fun heq => hx (heq ▸ hy)
      obtain ⟨U, V, hU, hV, hyU, hxV, hd⟩ := t2_separation hne
      exact ⟨U, V, hU, hV, singleton_subset_iff.mpr hyU,
        singleton_subset_iff.mpr hxV, hd⟩)
  obtain ⟨V, U, hV, hU, hKV, hxU, hd⟩ := hsep
  exact ⟨U, V, hU, hV, hxU (mem_singleton x), hKV, hd.symm⟩

theorem compact_subset_closed (K : Set X) (hK : SubspaceCompact K) : IsClosed K := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨U, V, hU, _, hxU, hKV, hd⟩ := compact_point_separation K hK x hx
  exact Filter.mem_of_superset (hU.mem_nhds hxU) fun y hy hyK =>
    Set.disjoint_left.mp hd hy (hKV hyK)

theorem disjoint_compact_separation (A B : Set X)
    (hA : SubspaceCompact A) (hB : SubspaceCompact B) (hAB : Disjoint A B) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧ Disjoint U V := by
  apply compact_separation_of_pointwise ((subspaceCompact_iff_isCompact A).mp hA)
  intro a ha
  obtain ⟨U, V, hU, hV, haU, hBV, hd⟩ :=
    compact_point_separation B hB a (fun hb => Set.disjoint_left.mp hAB ha hb)
  exact ⟨U, V, hU, hV, singleton_subset_iff.mpr haU, hBV, hd⟩

end Separation

/-- The extrema are actual values at points of the original domain.
No separation assumption on that domain is needed. -/
theorem continuous_real_extrema {X : Type u} [TopologicalSpace X] [Nonempty X]
    (f : X → ℝ) (hX : CoverCompact X) (hf : Continuous f) :
    ∃ xmin xmax : X, (∀ x, f xmin ≤ f x) ∧ (∀ x, f x ≤ f xmax) := by
  have hK : IsCompact (range f) := (subspaceCompact_iff_isCompact _).mp
    (continuous_compact_image f hX hf)
  obtain ⟨_, ⟨xmin, rfl⟩, hmin⟩ := hK.exists_isLeast (range_nonempty f)
  obtain ⟨_, ⟨xmax, rfl⟩, hmax⟩ := hK.exists_isGreatest (range_nonempty f)
  exact ⟨xmin, xmax, fun x => hmin (mem_range_self x),
    fun x => hmax (mem_range_self x)⟩

section Maps
variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

theorem compact_to_hausdorff_closed (f : X → Y) (hX : CoverCompact X)
    (hf : Continuous f) : IsClosedMap f := by
  intro F hF
  exact compact_subset_closed _
    (continuous_image_compact_subset f F (closed_subset_compact hX F hF) hf)

theorem compact_to_hausdorff_bijective (f : X → Y) (hX : CoverCompact X)
    (hf : Continuous f) (hb : Function.Bijective f) : IsHomeomorph f :=
  (Ch02.continuous_bijection_homeomorph_iff_closed f hf hb).mpr
    (compact_to_hausdorff_closed f hX hf)

theorem compact_to_hausdorff_injective (f : X → Y) (hX : CoverCompact X)
    (hf : Continuous f) (hi : Function.Injective f) : IsEmbedding f :=
  (IsClosedEmbedding.of_continuous_injective_isClosedMap hf hi
    (compact_to_hausdorff_closed f hX hf)).isEmbedding

theorem compact_to_hausdorff_surjective (f : X → Y) (hX : CoverCompact X)
    (hf : Continuous f) (hs : Function.Surjective f) : Ch03.QuotientMap f :=
  Ch03.continuous_closed_surjection_quotient f hf (compact_to_hausdorff_closed f hX hf) hs

end Maps
end D10Topology.Ch05
