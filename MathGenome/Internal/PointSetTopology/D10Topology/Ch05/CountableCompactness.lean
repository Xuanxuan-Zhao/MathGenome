import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.CountableCompactness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.Compactness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch04.FirstCountableSequences
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.ClosureCalculus

/-! Countable compactness and its cover, FIP, sequence, and accumulation criteria.
The library filter notions are connected explicitly to the paper's definitions.
Only the implication from limit point compactness to countable compactness uses T1. -/

open Set Filter
open scoped Topology
universe u v

namespace D10Topology.Ch05

abbrev CountableCoverCompact (X : Type u) [TopologicalSpace X] : Prop :=
  Specs.D10Topology.Ch05.CountableCompactness.CountableCoverCompact X
abbrev SequentiallyCompact (X : Type u) [TopologicalSpace X] : Prop :=
  Specs.D10Topology.Ch05.CountableCompactness.SequentiallyCompact X
abbrev LimitPointCompact (X : Type u) [TopologicalSpace X] : Prop :=
  Specs.D10Topology.Ch05.CountableCompactness.LimitPointCompact X

variable {X : Type u} [t : TopologicalSpace X]

theorem limitPointCompact_iff_neighborhoods (X : Type u) [t : TopologicalSpace X] :
    LimitPointCompact X ↔ ∀ A : Set X, A.Infinite → ∃ x : X, ∀ N : Set X,
      Ch01.Neighborhood t x N → (N ∩ (A \ {x})).Nonempty := by
  simp only [LimitPointCompact,
    Specs.D10Topology.Ch05.CountableCompactness.LimitPointCompact,
    Set.Nonempty, Ch01.derivedSet_eq_neighborhood_test, mem_ofPred_eq]

theorem sequence_clusters_iff_mapClusterPt (a : ℕ → X) (x : X) :
    Ch04.Clusters t a x ↔ MapClusterPt x atTop a := by
  rw [mapClusterPt_iff_frequently]
  constructor
  · intro h N hN
    exact frequently_atTop.mpr
      (h N ((Ch01.neighborhood_iff_mem_nhds t x N).mpr hN))
  · intro h N hN
    exact frequently_atTop.mp
      (h N ((Ch01.neighborhood_iff_mem_nhds t x N).mp hN))

theorem countableCoverCompact_iff_isCountablyCompact_univ
    (X : Type u) [TopologicalSpace X] :
    CountableCoverCompact X ↔ IsCountablyCompact (univ : Set X) := by
  constructor
  · intro h
    apply isCountablyCompact_iff_countable_open_cover.mpr
    intro U hU hcover
    obtain ⟨V, hVU, hV, hcoverV⟩ := h (range U) (countable_range U)
      (by rintro _ ⟨n, rfl⟩; exact hU n) (by simpa using hcover)
    -- Re-index the finite family by selecting one original index for each member.
    have hex : ∀ W : V, ∃ n, U n = W.val := fun W => hVU W.property
    choose f hf using hex
    classical
    let s : Finset ℕ := hV.toFinset.attach.image fun W => f ⟨W.val, hV.mem_toFinset.mp W.property⟩
    refine ⟨s, ?_⟩
    intro x hx
    obtain ⟨W, hWV, hxW⟩ := mem_sUnion.mp (hcoverV hx)
    have hn : f ⟨W, hWV⟩ ∈ s := by
      apply Finset.mem_image.mpr
      refine ⟨⟨W, hV.mem_toFinset.mpr hWV⟩, Finset.mem_attach _ _, rfl⟩
    exact mem_iUnion₂.mpr ⟨f ⟨W, hWV⟩, hn, (hf ⟨W, hWV⟩).symm ▸ hxW⟩
  · intro h U hU hOpen hcover
    obtain ⟨V, hVU, hV, hcoverV⟩ := h.elim_finite_subcover_image hU hOpen
      (by simpa only [sUnion_eq_biUnion] using hcover)
    exact ⟨V, hVU, hV, by simpa only [sUnion_eq_biUnion] using hcoverV⟩

theorem countableCoverCompact_iff_countablyCompactSpace
    (X : Type u) [TopologicalSpace X] :
    CountableCoverCompact X ↔ CountablyCompactSpace X :=
  (countableCoverCompact_iff_isCountablyCompact_univ X).trans isCountablyCompact_univ_iff

theorem sequentiallyCompact_iff_isSeqCompact_univ (X : Type u) [TopologicalSpace X] :
    SequentiallyCompact X ↔ IsSeqCompact (univ : Set X) := by
  simp only [SequentiallyCompact,
    Specs.D10Topology.Ch05.CountableCompactness.SequentiallyCompact,
    IsSeqCompact, mem_univ, forall_const, true_and, Ch04.sequence_converges_iff_tendsto]

theorem sequentiallyCompact_iff_seqCompactSpace (X : Type u) [TopologicalSpace X] :
    SequentiallyCompact X ↔ SeqCompactSpace X :=
  (sequentiallyCompact_iff_isSeqCompact_univ X).trans isSeqCompact_univ_iff

theorem countableCoverCompact_iff_closed_fip (X : Type u) [TopologicalSpace X] :
    CountableCoverCompact X ↔ ∀ A : Set (Set X), A.Countable →
      (∀ F ∈ A, IsClosed F) → HasFIP A → (⋂₀ A).Nonempty := by
  classical
  constructor
  · intro h A hA hclosed hfip
    by_contra hn
    have hc : (univ : Set X) ⊆ ⋃₀ (compl '' A) := by
      intro x _
      by_contra hx
      apply hn
      refine ⟨x, mem_sInter.mpr fun F hFA => ?_⟩
      by_contra hxF
      exact hx (mem_sUnion.mpr ⟨Fᶜ, ⟨F, hFA, rfl⟩, hxF⟩)
    obtain ⟨V, hVA, hV, hcover⟩ := h (compl '' A) (hA.image _)
      (by rintro _ ⟨F, hFA, rfl⟩; exact (hclosed F hFA).isOpen_compl) hc
    have hsub : compl '' V ⊆ A := by
      rintro _ ⟨F, hFV, rfl⟩
      obtain ⟨G, hGA, rfl⟩ := hVA hFV
      simpa using hGA
    obtain ⟨x, hx⟩ := hfip (compl '' V) hsub (hV.image _)
    obtain ⟨F, hFV, hxF⟩ := mem_sUnion.mp (hcover (mem_univ x))
    exact (mem_sInter.mp hx Fᶜ ⟨F, hFV, rfl⟩) hxF
  · intro h U hU hOpen hcover
    by_contra hn
    have hfip : HasFIP (compl '' U) := by
      intro B hBU hB
      have hsub : compl '' B ⊆ U := by
        rintro _ ⟨F, hFB, rfl⟩
        obtain ⟨V, hVU, rfl⟩ := hBU hFB
        simpa using hVU
      have hnot : ¬ (univ : Set X) ⊆ ⋃₀ (compl '' B) := by
        intro hc
        exact hn ⟨compl '' B, hsub, hB.image _, hc⟩
      obtain ⟨x, _, hx⟩ := Set.not_subset.mp hnot
      refine ⟨x, ?_⟩
      rwa [sInter_eq_compl_sUnion_compl]
    obtain ⟨x, hx⟩ := h (compl '' U) (hU.image _)
      (by rintro _ ⟨V, hV, rfl⟩; exact (hOpen V hV).isClosed_compl) hfip
    have hxnot : x ∉ ⋃₀ U := by
      simpa only [← compl_sUnion, mem_compl_iff] using hx
    exact hxnot (hcover (mem_univ x))

theorem countableCoverCompact_iff_sequence_cluster (X : Type u) [t : TopologicalSpace X] :
    CountableCoverCompact X ↔ ∀ a : ℕ → X, ∃ x : X, Ch04.Clusters t a x := by
  rw [countableCoverCompact_iff_isCountablyCompact_univ, isCountablyCompact_iff_seq_clusterPt]
  simp only [mem_univ, Filter.Eventually.of_forall, forall_const, true_and,
    sequence_clusters_iff_mapClusterPt]

theorem sequentiallyCompact_implies_countableCoverCompact
    (X : Type u) [TopologicalSpace X] (h : SequentiallyCompact X) : CountableCoverCompact X :=
  (countableCoverCompact_iff_isCountablyCompact_univ X).mpr
    (((sequentiallyCompact_iff_isSeqCompact_univ X).mp h).isCountablyCompact)

theorem firstCountable_countableCoverCompact_iff_sequentiallyCompact
    (X : Type u) [t : TopologicalSpace X] (h : Ch04.FirstCountable t) :
    CountableCoverCompact X ↔ SequentiallyCompact X := by
  let : FirstCountableTopology X := Ch04.firstCountable_iff_mathlib.mp h
  exact (countableCoverCompact_iff_isCountablyCompact_univ X).trans
    (isCountablyCompact_iff_isSeqCompact.trans (sequentiallyCompact_iff_isSeqCompact_univ X).symm)

theorem coverCompact_implies_countableCoverCompact
    (X : Type u) [TopologicalSpace X] (h : CoverCompact X) : CountableCoverCompact X :=
  fun U _ hU hc => h U hU hc

theorem countableCoverCompact_implies_limitPointCompact
    (X : Type u) [TopologicalSpace X] (h : CountableCoverCompact X) : LimitPointCompact X := by
  intro A hA
  obtain ⟨x, _, hx⟩ := IsCountablyCompact.exists_accPt_of_infinite
    ((countableCoverCompact_iff_isCountablyCompact_univ X).mp h) (subset_univ A) hA
  exact ⟨x, hx⟩

theorem coverCompact_implies_limitPointCompact
    (X : Type u) [TopologicalSpace X] (h : CoverCompact X) : LimitPointCompact X :=
  countableCoverCompact_implies_limitPointCompact X (coverCompact_implies_countableCoverCompact X h)

theorem countableCoverCompact_iff_limitPointCompact
    (X : Type u) [TopologicalSpace X] [T1Space X] :
    CountableCoverCompact X ↔ LimitPointCompact X := by
  rw [countableCoverCompact_iff_isCountablyCompact_univ,
    isCountablyCompact_iff_infinite_subset_has_accPt]
  constructor
  · intro h A hA
    obtain ⟨x, _, hx⟩ := h A (subset_univ A) hA
    exact ⟨x, hx⟩
  · intro h A _ hA
    obtain ⟨x, hx⟩ := h A hA
    exact ⟨x, mem_univ x, hx⟩

theorem countable_open_cover_finite_subcover (h : CountableCoverCompact X)
    {ι : Type v} [Countable ι] (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hc : univ ⊆ ⋃ i, U i) : ∃ s : Finset ι, univ ⊆ ⋃ i ∈ s, U i :=
  ((countableCoverCompact_iff_isCountablyCompact_univ X).mp h).elim_finite_subcover hU hc

theorem empty_space_countableCoverCompact (X : Type u) [TopologicalSpace X] [IsEmpty X] :
    CountableCoverCompact X :=
  coverCompact_implies_countableCoverCompact X (empty_space_compact X)

theorem empty_space_sequentiallyCompact (X : Type u) [TopologicalSpace X] [IsEmpty X] :
    SequentiallyCompact X := by
  intro a
  exact isEmptyElim (a 0)

theorem empty_space_limitPointCompact (X : Type u) [TopologicalSpace X] [IsEmpty X] :
    LimitPointCompact X :=
  countableCoverCompact_implies_limitPointCompact X (empty_space_countableCoverCompact X)

end D10Topology.Ch05
