import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.ProperPerfect
import MathGenome.Internal.PointSetTopology.D10Topology.Ch11.LocalCompactConventions

/-!
Proper and perfect maps, paper.tex d10:11:proper-perfect and
d10:11:proper-calculus. The first bridge below checks the exact meaning of
Mathlib's `IsProperMap`; the second implication needs no separation axiom.
Only the reverse compact-preimage bridge installs Hausdorffness and weak
local compactness, both obtained from the stated LCH target hypothesis.
All source spaces and fibers may be empty, and maps need not be onto.
-/

open Set Topology
universe u v w

namespace D10Topology.Ch11

theorem perfect_iff_isProperMap {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Perfect f ↔ IsProperMap f :=
  isProperMap_iff_isClosedMap_and_compact_fibers.symm

theorem proper_of_isProperMap {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : IsProperMap f) : Proper f :=
  ⟨hf.continuous, fun _ hK => hf.isCompact_preimage hK⟩

theorem isProperMap_iff_proper {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (hY : LCH Y) (f : X → Y) :
    IsProperMap f ↔ Proper f := by
  let : T2Space Y := hY.2
  let : WeaklyLocallyCompactSpace Y :=
    (locallyCompact_iff_weaklyLocallyCompactSpace Y).mp hY.1
  -- The library reverse implication requires a Hausdorff compactly coherent
  -- target. Weak local compactness supplies compact coherence, with no
  -- corresponding condition on X.
  exact ⟨proper_of_isProperMap, fun hf =>
    isProperMap_iff_isCompact_preimage.mpr ⟨hf.1, fun _ hK => hf.2 _ hK⟩⟩

theorem proper_of_perfect {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Perfect f) : Proper f :=
  proper_of_isProperMap ((perfect_iff_isProperMap f).mp hf)

theorem perfect_of_proper {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (hY : LCH Y) {f : X → Y}
    (hf : Proper f) : Perfect f :=
  (perfect_iff_isProperMap f).mpr ((isProperMap_iff_proper hY f).mpr hf)

theorem proper_iff_perfect {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (hY : LCH Y) (f : X → Y) :
    Proper f ↔ Perfect f :=
  ⟨perfect_of_proper hY, proper_of_perfect⟩

theorem proper_comp {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} {g : Y → Z} (hg : Proper g) (hf : Proper f) :
    Proper (g ∘ f) :=
  ⟨hg.1.comp hf.1, fun K hK => hf.2 (g ⁻¹' K) (hg.2 K hK)⟩

theorem proper_closed_embedding {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : IsClosedEmbedding f) : Proper f :=
  ⟨hf.continuous, fun _ hK => hf.isCompact_preimage hK⟩

theorem proper_closed_inclusion {X : Type u} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) : Proper (Subtype.val : A → X) :=
  proper_closed_embedding hA.isClosedEmbedding_subtypeVal

theorem proper_of_compact_domain {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space Y]
    {f : X → Y} (hf : Continuous f) : Proper f :=
  ⟨hf, fun _ hK => (hK.isClosed.preimage hf).isCompact⟩

theorem compact_domain_of_proper {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    {f : X → Y} (hf : Proper f) : CompactSpace X :=
  isCompact_univ_iff.mp (by simpa only [preimage_univ] using hf.2 univ isCompact_univ)

end D10Topology.Ch11
