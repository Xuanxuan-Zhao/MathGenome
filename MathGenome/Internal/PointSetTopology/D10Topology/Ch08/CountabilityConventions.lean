import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.CountabilityConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch04.FirstCountableSequences

/-!
The four countability conventions in paper.tex, d10:08:definitions.
First countability and local-base refinement reuse the chapter 4 objects and
proofs. The other three conditions use canonical Mathlib classes, justified
by exact equivalences with the paper's formulations.
-/

open Set TopologicalSpace
open scoped Topology
universe u v

namespace D10Topology.Ch08

/-- The exact first-countability object used for chapter 4's sequence tests. -/
abbrev FirstCountable {X : Type u} (t : TopologicalSpace X) : Prop :=
  Ch04.FirstCountable t

/-- The canonical class, identified with a countable basis below. -/
abbrev SecondCountable {X : Type u} (t : TopologicalSpace X) : Prop :=
  @SecondCountableTopology X t

/-- The canonical class, with density expressed by closure below. -/
abbrev Separable {X : Type u} (t : TopologicalSpace X) : Prop :=
  @SeparableSpace X t

/-- The canonical class, identified with the open-subcover condition below. -/
abbrev Lindelof {X : Type u} (t : TopologicalSpace X) : Prop :=
  @LindelofSpace X t

variable {X : Type u} [t : TopologicalSpace X]

theorem firstCountable_iff_mathlib : Ch04.FirstCountable t ↔ FirstCountableTopology X :=
  Ch04.firstCountable_iff_mathlib

theorem secondCountable_iff_countable_basis :
    SecondCountableTopology X ↔ ∃ B : Set (Set X), B.Countable ∧ Ch01.BasisFor t B := by
  constructor
  · intro h
    let := h
    obtain ⟨B, hc, _, hB⟩ := exists_countable_basis X
    exact ⟨B, hc, (Ch01.basis_iff_mathlib t B).mpr hB⟩
  · rintro ⟨B, hc, hB⟩
    exact ((Ch01.basis_iff_mathlib t B).mp hB).secondCountableTopology hc

theorem separable_iff_countable_dense :
    SeparableSpace X ↔ ∃ D : Set X, D.Countable ∧ closure D = univ := by
  constructor
  · intro h
    obtain ⟨D, hc, hd⟩ := h.exists_countable_dense
    exact ⟨D, hc, hd.closure_eq⟩
  · rintro ⟨D, hc, hd⟩
    exact ⟨⟨D, hc, dense_iff_closure_eq.mpr hd⟩⟩

theorem lindelof_iff_countable_subcover :
    LindelofSpace X ↔
      ∀ {ι : Type u} (U : ι → Set X), (∀ i, IsOpen (U i)) →
        (⋃ i, U i) = univ → ∃ J : Set ι, J.Countable ∧ (⋃ i ∈ J, U i) = univ := by
  rw [← isLindelof_univ_iff, isLindelof_iff_countable_subcover]
  simp only [univ_subset_iff]

theorem lindelof_indexed_countable_subcover (h : LindelofSpace X)
    {ι : Type v} (U : ι → Set X) (ho : ∀ i, IsOpen (U i))
    (hc : (⋃ i, U i) = univ) :
    ∃ J : Set ι, J.Countable ∧ (⋃ i ∈ J, U i) = univ := by
  obtain ⟨J, hJ, hcov⟩ := h.isLindelof_univ.elim_countable_subcover U ho hc.ge
  exact ⟨J, hJ, univ_subset_iff.mp hcov⟩

theorem countable_localBase_open_refinement (x : X) (L : Set (Set X))
    (hc : L.Countable) (hL : Ch01.LocalBase t x L) :
    ∃ M : Set (Set X), M.Countable ∧ Ch01.LocalBase t x M ∧
      (∀ V ∈ M, IsOpen V) ∧ (∀ V ∈ M, ∃ N ∈ L, V ⊆ N) :=
  Ch04.countable_localBase_open_refinement x L hc hL

theorem countable_localBase_decreasing_open_refinement (x : X) (L : Set (Set X))
    (hc : L.Countable) (hL : Ch01.LocalBase t x L) :
    ∃ U : ℕ → Set X, Antitone U ∧ (∀ n, IsOpen (U n)) ∧
      Ch01.LocalBase t x (range U) ∧ (∀ n, ∃ N ∈ L, U n ⊆ N) := by
  obtain ⟨M, hMc, hM, ho, href⟩ := countable_localBase_open_refinement x L hc hL
  obtain ⟨V, hV⟩ := Ch04.countable_localBase_enumeration x M hMc hM
  have hVM : ∀ n, V n ∈ M := fun n => hV ▸ mem_range_self n
  have hbase : Ch01.LocalBase t x (range V) := hV.symm ▸ hM
  obtain ⟨ha, hop, hb⟩ := Ch04.decreasing_open_localBase x V hbase
    (fun n => ho _ (hVM n))
  refine ⟨(fun n => ⋂ k ≤ n, V k), ha, hop, hb, ?_⟩
  intro n
  obtain ⟨N, hNL, hVN⟩ := href _ (hVM n)
  refine ⟨N, hNL, ?_⟩
  intro z hz
  exact hVN (mem_iInter₂.mp hz n le_rfl)

theorem firstCountable_iff_decreasing_open_localBases :
    Ch04.FirstCountable t ↔
      ∀ x : X, ∃ U : ℕ → Set X, Antitone U ∧ (∀ n, IsOpen (U n)) ∧
        Ch01.LocalBase t x (range U) := by
  constructor
  · intro h x
    exact Ch04.firstCountableAt_decreasing_open_localBase x (h x)
  · intro h x
    obtain ⟨U, _, _, hU⟩ := h x
    exact ⟨range U, countable_range U, hU⟩

theorem empty_countability_properties [IsEmpty X] :
    Ch04.FirstCountable t ∧ SecondCountableTopology X ∧ SeparableSpace X ∧ LindelofSpace X := by
  refine ⟨(fun x => isEmptyElim x), ?_, ?_, ?_⟩ <;> infer_instance

end D10Topology.Ch08
