import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.TopologicalFoundations

/-! Foundations of Chapter 1. The order on `TopologicalSpace` is reverse
inclusion of open families: finer topologies are smaller in Lean's order. -/

open Set
open scoped Topology
universe u

namespace D10Topology.Ch01

/-- The one canonical notion of topology used throughout the development. -/
abbrev Topology (X : Type u) : Type u := TopologicalSpace X

@[instance_reducible] def discrete (X : Type u) : TopologicalSpace X := ⊥
@[instance_reducible] def indiscrete (X : Type u) : TopologicalSpace X := ⊤

/-- σ is finer than τ exactly when every τ-open set is σ-open. -/
def Finer {X : Type u} (σ τ : TopologicalSpace X) : Prop :=
  openSets τ ⊆ openSets σ

@[instance_reducible] def generated {X : Type u} (A : Set (Set X)) : TopologicalSpace X :=
  TopologicalSpace.generateFrom A

/-- Intersection of open families; it is a supremum in Lean's reverse order. -/
@[instance_reducible] def intersection {X : Type u} (T : Set (TopologicalSpace X)) : TopologicalSpace X :=
  sSup T

theorem open_axioms {X : Type u} (t : TopologicalSpace X) :
    OpenFamilyAxioms (openSets t) := by
  let := t
  exact ⟨isOpen_empty, isOpen_univ, fun _ h => isOpen_sUnion h,
    fun _ hA h => hA.isOpen_sInter h⟩

theorem open_characterization {X : Type u} (O : Set (Set X)) :
    OpenFamilyAxioms O ↔ ∃! t : TopologicalSpace X, openSets t = O := by
  constructor
  · intro h
    let t : TopologicalSpace X := {
      IsOpen := fun U => U ∈ O
      isOpen_univ := h.univ_mem
      isOpen_inter := fun U V hU hV => by
        have hp := h.finite_sInter_mem {U, V} (by simp) (by
          simp only [insert_subset_iff, singleton_subset_iff]
          exact ⟨hU, hV⟩)
        simpa using hp
      isOpen_sUnion := h.sUnion_mem }
    refine ⟨t, rfl, ?_⟩
    intro s hs
    apply TopologicalSpace.ext
    funext U
    exact congrArg (fun A : Set (Set X) => U ∈ A) hs
  · rintro ⟨t, ht, _⟩
    rw [← ht]
    exact open_axioms t

theorem closed_iff_open_complement {X : Type u} (t : TopologicalSpace X) (F : Set X) :
    F ∈ closedSets t ↔ Fᶜ ∈ openSets t := by
  exact (@isOpen_compl_iff X F t).symm

theorem discrete_opens (X : Type u) : openSets (discrete X) = univ := by
  ext U
  exact iff_true_intro trivial

theorem indiscrete_opens (X : Type u) : openSets (indiscrete X) = {∅, univ} := by
  ext U
  exact (TopologicalSpace.isOpen_top_iff U).trans (by simp)

theorem finer_iff_le {X : Type u} (σ τ : TopologicalSpace X) : Finer σ τ ↔ σ ≤ τ :=
  Iff.rfl

theorem closed_axioms {X : Type u} (t : TopologicalSpace X) :
    ClosedFamilyAxioms (closedSets t) := by
  let := t
  exact ⟨isClosed_empty, isClosed_univ, fun _ h => isClosed_sInter h,
    fun _ hA h => hA.isClosed_sUnion h⟩

theorem closed_characterization {X : Type u} (C : Set (Set X)) :
    ClosedFamilyAxioms C ↔ ∃! t : TopologicalSpace X, closedSets t = C := by
  constructor
  · intro h
    let t : TopologicalSpace X := TopologicalSpace.ofClosed C h.empty_mem h.sInter_mem
      (fun U hU V hV => by
        have hp := h.finite_sUnion_mem {U, V} (by simp) (by
          simp only [insert_subset_iff, singleton_subset_iff]
          exact ⟨hU, hV⟩)
        simpa using hp)
    have ht : closedSets t = C := by
      ext F
      change IsClosed[t] F ↔ F ∈ C
      rw [← @isOpen_compl_iff X F t]
      change Fᶜᶜ ∈ C ↔ F ∈ C
      simp
    refine ⟨t, ht, ?_⟩
    intro s hs
    apply TopologicalSpace.ext_isClosed
    intro F
    change F ∈ closedSets s ↔ F ∈ closedSets t
    rw [hs, ht]
  · rintro ⟨t, ht, _⟩
    rw [← ht]
    exact closed_axioms t

theorem generated_smallest {X : Type u} (A : Set (Set X)) :
    A ⊆ openSets (generated A) ∧
      ∀ t : TopologicalSpace X, A ⊆ openSets t →
        openSets (generated A) ⊆ openSets t := by
  exact ⟨fun _ hs => TopologicalSpace.isOpen_generateFrom_of_mem hs,
    fun _ ht => TopologicalSpace.le_generateFrom_iff_subset_isOpen.mpr ht⟩

theorem intersection_opens {X : Type u} (T : Set (TopologicalSpace X)) :
    openSets (intersection T) = ⋂ t ∈ T, openSets t :=
  by
    ext U
    simp only [openSets, mem_ofPred_eq, mem_iInter]
    exact isOpen_sSup_iff

theorem intersection_family_axioms {X : Type u} (T : Set (TopologicalSpace X)) :
    OpenFamilyAxioms (⋂ t ∈ T, openSets t) := by
  rw [← intersection_opens T]
  exact open_axioms _

/-- A family with just ∅, A, X is always a topology. -/
private theorem three_set_family {X : Type u} (A : Set X) :
    OpenFamilyAxioms {∅, A, univ} := by
  classical
  have union_mem : ∀ S : Set (Set X), S ⊆ {∅, A, univ} → ⋃₀ S ∈ ({∅, A, univ} : Set (Set X)) := by
    intro S hS
    by_cases hu : univ ∈ S
    · have heq : ⋃₀ S = univ := by
        apply eq_univ_of_univ_subset
        exact subset_sUnion_of_mem hu
      simp [heq]
    by_cases ha : A ∈ S
    · have heq : ⋃₀ S = A := by
        apply Subset.antisymm _ (subset_sUnion_of_mem ha)
        apply sUnion_subset
        intro U hU
        rcases (by simpa using hS hU : U = ∅ ∨ U = A ∨ U = univ) with h | h | h
        · simp [h]
        · simp [h]
        · exact (hu (h ▸ hU)).elim
      simp [heq]
    · have heq : ⋃₀ S = ∅ := by
        apply sUnion_eq_empty.mpr
        intro U hU
        rcases (by simpa using hS hU : U = ∅ ∨ U = A ∨ U = univ) with h | h | h
        · exact h
        · exact (ha (h ▸ hU)).elim
        · exact (hu (h ▸ hU)).elim
      simp [heq]
  refine ⟨by simp, by simp, union_mem, ?_⟩
  intro S hS hSO
  induction S, hS using Set.Finite.induction_on with
  | empty => simp
  | @insert U S hUS hfin ih =>
    have hU : U = ∅ ∨ U = A ∨ U = univ := by simpa using hSO (by simp : U ∈ insert U S)
    have hI := ih (fun V hV => hSO (by simp [hV]))
    have hI' : ⋂₀ S = ∅ ∨ ⋂₀ S = A ∨ ⋂₀ S = univ := by simpa using hI
    rw [sInter_insert]
    rcases hU with h | h | h <;> rcases hI' with k | k | k <;> simp [h, k]

theorem union_counterexample :
    ∃ τ₁ τ₂ : TopologicalSpace (Fin 3),
      openSets τ₁ = {∅, {(0 : Fin 3)}, univ} ∧
      openSets τ₂ = {∅, {(1 : Fin 3)}, univ} ∧
      {(0 : Fin 3)} ∈ openSets τ₁ ∪ openSets τ₂ ∧
      {(1 : Fin 3)} ∈ openSets τ₁ ∪ openSets τ₂ ∧
      ({(0 : Fin 3)} ∪ {(1 : Fin 3)}) ∉ openSets τ₁ ∪ openSets τ₂ ∧
      ¬ OpenFamilyAxioms (openSets τ₁ ∪ openSets τ₂) := by
  obtain ⟨τ₁, h₁, _⟩ := (open_characterization _).mp (three_set_family {(0 : Fin 3)})
  obtain ⟨τ₂, h₂, _⟩ := (open_characterization _).mp (three_set_family {(1 : Fin 3)})
  have ha : {(0 : Fin 3)} ∈ openSets τ₁ ∪ openSets τ₂ := by rw [h₁, h₂]; simp
  have hb : {(1 : Fin 3)} ∈ openSets τ₁ ∪ openSets τ₂ := by rw [h₁, h₂]; simp
  have hn : ({(0 : Fin 3)} ∪ {(1 : Fin 3)}) ∉ openSets τ₁ ∪ openSets τ₂ := by
    rw [h₁, h₂]
    simp only [mem_union, mem_insert_iff, mem_singleton_iff]
    simp only [Set.ext_iff]
    decide
  refine ⟨τ₁, τ₂, h₁, h₂, ha, hb, hn, ?_⟩
  intro h
  have hu := h.sUnion_mem {{(0 : Fin 3)}, {(1 : Fin 3)}} (by
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨ha, hb⟩)
  apply hn
  simpa using hu

end D10Topology.Ch01
