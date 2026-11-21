import MathGenome.Internal.MultivariableAnalysis.D04.C01.Connectedness
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.Components

/-! Connected components in arbitrary spaces and in open Euclidean domains.
The canonical definition is the literal union from the manuscript, and the
standard-component bridge below identifies its relative-topology meaning. -/
noncomputable section
open Set
universe u
namespace D04

abbrev componentWithin {X : Type u} [TopologicalSpace X] (U : Set X) (a : X) : Set X :=
  Specs.D04.C01.Components.Model.componentWithin U a

abbrev IsMaximalConnectedWithin {X : Type u} [TopologicalSpace X]
    (U C : Set X) : Prop :=
  Specs.D04.C01.Components.Model.IsMaximalConnectedWithin U C

abbrev componentsWithin {X : Type u} [TopologicalSpace X] (U : Set X) : Set (Set X) :=
  Specs.D04.C01.Components.Model.componentsWithin U

theorem componentWithin_subset {X : Type u} [TopologicalSpace X]
    (U : Set X) (a : X) : componentWithin U a ⊆ U := by
  rintro x ⟨C, hC, hx⟩
  exact hC.1 hx

theorem mem_componentWithin {X : Type u} [TopologicalSpace X]
    (U : Set X) (a : X) (ha : a ∈ U) : a ∈ componentWithin U a :=
  mem_sUnion_of_mem (mem_singleton a)
    ⟨singleton_subset_iff.mpr ha, isPreconnected_singleton, mem_singleton a⟩

theorem componentWithin_connected {X : Type u} [TopologicalSpace X]
    (U : Set X) (a : X) : IsPreconnected (componentWithin U a) :=
  isPreconnected_sUnion a _ (fun _ h => h.2.2) (fun _ h => h.2.1)

theorem subset_componentWithin {X : Type u} [TopologicalSpace X]
    (U C : Set X) (a : X) (hCU : C ⊆ U) (hC : IsPreconnected C) (ha : a ∈ C) :
    C ⊆ componentWithin U a :=
  subset_sUnion_of_mem ⟨hCU, hC, ha⟩

/-- This also verifies that connected subsets of the ambient space give the
usual components for the relative topology on U. -/
theorem componentWithin_eq_standard {X : Type u} [TopologicalSpace X]
    (U : Set X) (a : X) : componentWithin U a = connectedComponentIn U a := by
  apply Subset.antisymm
  · rintro x ⟨C, hC, hx⟩
    exact hC.2.1.subset_connectedComponentIn hC.2.2 hC.1 hx
  · by_cases ha : a ∈ U
    · exact subset_componentWithin U _ a (connectedComponentIn_subset U a)
        isPreconnected_connectedComponentIn (mem_connectedComponentIn ha)
    · rw [connectedComponentIn_eq_empty ha]
      exact empty_subset _

theorem componentWithin_unique_maximal {X : Type u} [TopologicalSpace X]
    (U : Set X) (a : X) (ha : a ∈ U) :
    a ∈ componentWithin U a ∧ IsMaximalConnectedWithin U (componentWithin U a) ∧
      ∀ C : Set X, a ∈ C → IsMaximalConnectedWithin U C → C = componentWithin U a := by
  have hmax : IsMaximalConnectedWithin U (componentWithin U a) := by
    refine ⟨componentWithin_subset U a, componentWithin_connected U a, ?_⟩
    intro B hCB hBU hB
    exact (subset_componentWithin U B a hBU hB (hCB (mem_componentWithin U a ha))).antisymm hCB
  refine ⟨mem_componentWithin U a ha, hmax, ?_⟩
  intro C haC hC
  exact (hC.2.2 _ (subset_componentWithin U C a hC.1 hC.2.1 haC)
    (componentWithin_subset U a) (componentWithin_connected U a)).symm

theorem componentWithin_eq_of_mem {X : Type u} [TopologicalSpace X]
    (U : Set X) (a b : X) (hb : b ∈ componentWithin U a) :
    componentWithin U a = componentWithin U b := by
  simp only [componentWithin_eq_standard] at hb ⊢
  exact connectedComponentIn_eq hb

theorem componentWithin_eq_of_meet {X : Type u} [TopologicalSpace X]
    (U : Set X) (a b : X) (h : (componentWithin U a ∩ componentWithin U b).Nonempty) :
    componentWithin U a = componentWithin U b := by
  obtain ⟨x, hax, hbx⟩ := h
  exact (componentWithin_eq_of_mem U a x hax).trans (componentWithin_eq_of_mem U b x hbx).symm

theorem componentsWithin_partition {X : Type u} [TopologicalSpace X] (U : Set X) :
    ⋃₀ componentsWithin U = U ∧
      (∀ C ∈ componentsWithin U, C.Nonempty ∧ C ⊆ U ∧ IsPreconnected C) ∧
      ∀ C ∈ componentsWithin U, ∀ D ∈ componentsWithin U, C ≠ D → Disjoint C D := by
  refine ⟨?_, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro x ⟨C, ⟨a, ha, rfl⟩, hx⟩
      exact componentWithin_subset U a hx
    · intro x hx
      exact mem_sUnion_of_mem (mem_componentWithin U x hx) ⟨x, hx, rfl⟩
  · rintro C ⟨a, ha, rfl⟩
    exact ⟨⟨a, mem_componentWithin U a ha⟩, componentWithin_subset U a,
      componentWithin_connected U a⟩
  · rintro C ⟨a, ha, rfl⟩ D ⟨b, hb, rfl⟩ hne
    apply Set.disjoint_left.mpr
    intro x hax hbx
    exact hne (componentWithin_eq_of_meet U a b ⟨x, hax, hbx⟩)

theorem componentsWithin_unique_member {X : Type u} [TopologicalSpace X]
    (U : Set X) (x : X) (hx : x ∈ U) :
    ∃! C : Set X, C ∈ componentsWithin U ∧ x ∈ C := by
  refine ⟨componentWithin U x, ⟨⟨x, hx, rfl⟩, mem_componentWithin U x hx⟩, ?_⟩
  rintro C ⟨⟨a, ha, rfl⟩, hax⟩
  exact componentWithin_eq_of_mem U a x hax

theorem componentsWithin_empty {X : Type u} [TopologicalSpace X] :
    componentsWithin (∅ : Set X) = ∅ := by
  ext C
  simp [componentsWithin, Specs.D04.C01.Components.Model.componentsWithin]

/-- Every point of a component has a connected ambient ball that stays in
that component. This proof works unchanged in dimension zero. -/
theorem open_componentWithin {n : ℕ} (U : Set (E n)) (hU : Open U) (a : E n) :
    Open (componentWithin U a) := by
  intro x hx
  obtain ⟨r, hr, hball⟩ := hU x (componentWithin_subset U a hx)
  refine ⟨r, hr, ?_⟩
  have hconn : IsPreconnected (ball x r) := by
    rw [ball_eq_metric]
    exact (convex_ball x r).isPreconnected
  have hsub := subset_componentWithin U (ball x r) x hball hconn (by
    rw [ball_eq_metric]
    exact Metric.mem_ball_self hr)
  rw [← componentWithin_eq_of_mem U a x hx] at hsub
  exact hsub

theorem componentWithin_polygonallyConnected {n : ℕ} (U : Set (E n))
    (hU : Open U) (a : E n) : PolygonallyConnected (componentWithin U a) :=
  open_connected_polygonallyConnected _ (open_componentWithin U hU a)
    (componentWithin_connected U a)

theorem componentWithin_dimension_zero (U : Set (E 0)) (a : E 0) (ha : a ∈ U) :
    componentWithin U a = U := by
  apply (componentWithin_subset U a).antisymm
  intro x _
  have hxa : x = a := Subsingleton.elim _ _
  simpa only [hxa] using mem_componentWithin U a ha

end D04
