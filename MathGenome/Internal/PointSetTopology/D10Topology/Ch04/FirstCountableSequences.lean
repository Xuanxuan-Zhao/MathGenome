import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.FirstCountableSequences
import MathGenome.Internal.PointSetTopology.D10Topology.Ch04.NetTests

/-!
Sequence criteria and countable local bases from paper.tex, Chapters 4 and 8.
We retain the paper's arbitrary-neighborhood convention. Taking interiors
produces an open refinement; finite prefix intersections make it decreasing.
Choice of a point in each intersection with A then gives the closure sequence.
-/

open Set Filter
open scoped Topology
universe u v

namespace D10Topology.Ch04

abbrev FirstCountableAt {X : Type u} (t : TopologicalSpace X) (x : X) : Prop :=
  Specs.D10Topology.Ch04.FirstCountableSequences.FirstCountableAt t x

abbrev FirstCountable {X : Type u} (t : TopologicalSpace X) : Prop :=
  Specs.D10Topology.Ch04.FirstCountableSequences.FirstCountable t

variable {X : Type u} [t : TopologicalSpace X]

theorem firstCountableAt_iff_countablyGenerated (x : X) :
    FirstCountableAt t x ↔ (𝓝 x).IsCountablyGenerated := by
  constructor
  · rintro ⟨L, hc, hL⟩
    exact (Filter.HasCountableBasis.mk ((Ch01.localBase_iff_hasBasis t x L).mp hL)
      hc).isCountablyGenerated
  · intro h
    let := h
    obtain ⟨U, hU⟩ := Filter.exists_antitone_basis (𝓝 x)
    refine ⟨range U, countable_range U, ?_⟩
    apply (Ch01.localBase_iff_hasBasis t x _).mpr
    constructor
    intro N
    constructor
    · intro hN
      obtain ⟨n, hn⟩ := hU.mem_iff.mp hN
      exact ⟨U n, mem_range_self n, hn⟩
    · rintro ⟨V, ⟨n, rfl⟩, hVN⟩
      exact mem_of_superset (hU.mem n) hVN

theorem firstCountable_iff_mathlib : FirstCountable t ↔ FirstCountableTopology X := by
  constructor
  · intro h
    exact ⟨fun x => (firstCountableAt_iff_countablyGenerated x).mp (h x)⟩
  · intro h x
    exact (firstCountableAt_iff_countablyGenerated x).mpr (h.nhds_generated_countable x)

theorem countable_localBase_open_refinement (x : X) (L : Set (Set X))
    (hc : L.Countable) (hL : Ch01.LocalBase t x L) :
    ∃ M : Set (Set X), M.Countable ∧ Ch01.LocalBase t x M ∧
      (∀ V ∈ M, IsOpen V) ∧ (∀ V ∈ M, ∃ N ∈ L, V ⊆ N) := by
  refine ⟨interior '' L, hc.image interior, ?_, ?_, ?_⟩
  · constructor
    · rintro V ⟨N, hNL, rfl⟩
      obtain ⟨U, hU, hxU, hUN⟩ := hL.1 N hNL
      exact ⟨interior N, isOpen_interior,
        (interior_maximal hUN hU) hxU, Subset.rfl⟩
    · intro N hN
      obtain ⟨V, hVL, hVN⟩ := hL.2 N hN
      exact ⟨interior V, mem_image_of_mem interior hVL, interior_subset.trans hVN⟩
  · rintro V ⟨N, _, rfl⟩
    exact isOpen_interior
  · rintro V ⟨N, hNL, rfl⟩
    exact ⟨N, hNL, interior_subset⟩

theorem countable_localBase_enumeration (x : X) (L : Set (Set X))
    (hc : L.Countable) (hL : Ch01.LocalBase t x L) :
    ∃ U : ℕ → Set X, range U = L := by
  obtain ⟨V, hVL, _⟩ := hL.2 univ (Ch01.neighborhood_univ t x)
  obtain ⟨U, hU⟩ := hc.exists_eq_range ⟨V, hVL⟩
  exact ⟨U, hU.symm⟩

theorem decreasing_open_localBase (x : X) (U : ℕ → Set X)
    (hL : Ch01.LocalBase t x (range U)) (hU : ∀ n, IsOpen (U n)) :
    Antitone (fun n => ⋂ k ≤ n, U k) ∧
      (∀ n, IsOpen (⋂ k ≤ n, U k)) ∧
      Ch01.LocalBase t x (range (fun n => ⋂ k ≤ n, U k)) := by
  have hopen : ∀ n, IsOpen (⋂ k ≤ n, U k) := fun n =>
    (finite_le_nat n).isOpen_biInter (fun k _ => hU k)
  have hx : ∀ n, x ∈ ⋂ k ≤ n, U k := by
    intro n
    exact mem_iInter₂.mpr (fun k _ => Ch01.neighborhood_contains t x (U k)
      (hL.1 (U k) (mem_range_self k)))
  refine ⟨?_, hopen, ?_⟩
  · intro n m hnm z hz
    exact mem_iInter₂.mpr (fun k hkn => mem_iInter₂.mp hz k (hkn.trans hnm))
  · constructor
    · rintro V ⟨n, rfl⟩
      exact ⟨_, hopen n, hx n, Subset.rfl⟩
    · intro N hN
      obtain ⟨V, ⟨n, rfl⟩, hVN⟩ := hL.2 N hN
      refine ⟨_, mem_range_self n, ?_⟩
      intro z hz
      exact hVN (mem_iInter₂.mp hz n le_rfl)

theorem firstCountableAt_decreasing_open_localBase (x : X) (h : FirstCountableAt t x) :
    ∃ U : ℕ → Set X, Antitone U ∧ (∀ n, IsOpen (U n)) ∧
      Ch01.LocalBase t x (range U) := by
  obtain ⟨L, hc, hL⟩ := h
  obtain ⟨M, hMc, hM, ho, _⟩ := countable_localBase_open_refinement x L hc hL
  obtain ⟨U, hU⟩ := countable_localBase_enumeration x M hMc hM
  have hb : Ch01.LocalBase t x (range U) := hU.symm ▸ hM
  have hop : ∀ n, IsOpen (U n) := fun n => ho _ (hU ▸ mem_range_self n)
  exact ⟨_, decreasing_open_localBase x U hb hop⟩

theorem sequence_converges_iff_tendsto (a : ℕ → X) (x : X) :
    Converges t a x ↔ Tendsto a atTop (𝓝 x) := by
  constructor
  · intro h N hN
    exact eventually_atTop.mpr (h N ((Ch01.neighborhood_iff_mem_nhds t x N).mpr hN))
  · intro h N hN
    exact eventually_atTop.mp (h ((Ch01.neighborhood_iff_mem_nhds t x N).mp hN))

theorem closure_iff_exists_sequence (h : FirstCountable t) (A : Set X) (x : X) :
    x ∈ closure A ↔ ∃ a : ℕ → X, (∀ n, a n ∈ A) ∧ Converges t a x := by
  constructor
  · intro hx
    obtain ⟨U, hanti, _, hU⟩ := firstCountableAt_decreasing_open_localBase x (h x)
    have hex : ∀ n, ∃ a, a ∈ U n ∧ a ∈ A := fun n =>
      (Ch01.closure_neighborhood_test A x).mp hx (U n) (hU.1 _ (mem_range_self n))
    choose a haU haA using hex
    refine ⟨a, haA, ?_⟩
    intro N hN
    obtain ⟨V, ⟨n, rfl⟩, hVN⟩ := hU.2 N hN
    exact ⟨n, fun m hnm => hVN (hanti hnm (haU m))⟩
  · rintro ⟨a, ha, hx⟩
    exact mem_closure_of_net A a x ha hx

theorem closed_iff_sequence_limits (h : FirstCountable t) (A : Set X) :
    IsClosed A ↔
      ∀ (a : ℕ → X) (x : X), (∀ n, a n ∈ A) → Converges t a x → x ∈ A := by
  constructor
  · intro hA a x ha hx
    exact hA.closure_subset (mem_closure_of_net A a x ha hx)
  · intro hA
    apply isClosed_of_closure_subset
    intro x hx
    obtain ⟨a, ha, hax⟩ := (closure_iff_exists_sequence h A x).mp hx
    exact hA a x ha hax

variable {Y : Type v} [tY : TopologicalSpace Y]

theorem continuousAt_iff_sequence_limits (f : X → Y) (x : X)
    (h : FirstCountableAt t x) :
    ContinuousAt f x ↔
      ∀ a : ℕ → X, Converges t a x → Converges tY (f ∘ a) (f x) := by
  let := (firstCountableAt_iff_countablyGenerated x).mp h
  simp only [sequence_converges_iff_tendsto]
  exact Filter.tendsto_iff_seq_tendsto

theorem continuous_iff_sequence_limits (h : FirstCountable t) (f : X → Y) :
    Continuous f ↔ ∀ (a : ℕ → X) (x : X),
      Converges t a x → Converges tY (f ∘ a) (f x) := by
  rw [Ch02.continuous_iff_pointwise]
  constructor
  · intro hf a x ha
    exact (continuousAt_iff_sequence_limits f x (h x)).mp (hf x) a ha
  · intro hf x
    exact (continuousAt_iff_sequence_limits f x (h x)).mpr (fun a ha => hf a x ha)

end D10Topology.Ch04
