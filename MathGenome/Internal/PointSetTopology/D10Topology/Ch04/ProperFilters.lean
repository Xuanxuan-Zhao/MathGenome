import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.ProperFilters
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.BasesAndNeighborhoods

/-! Proper filters and their exact set-family descriptions, paper.tex Chapter 4.
The order bridge reverses family inclusion. Empty types and the empty finite
intersection are retained; no separation or countability assumptions are used. -/

open Set Filter
open scoped Topology
universe u v
namespace D10Topology.Ch04
open D10Topology.Ch01

def ProperFilter (X : Type u) : Type u :=
  {F : Filter X // F.NeBot}

def ProperFamily {X : Type u} (A : Set (Set X)) : Prop :=
  A.Nonempty ∧ (∅ : Set X) ∉ A ∧
    (∀ U ∈ A, ∀ V, U ⊆ V → V ∈ A) ∧
    (∀ U ∈ A, ∀ V ∈ A, U ∩ V ∈ A)

def FilterBase {X : Type u} (B : Set (Set X)) : Prop :=
  B.Nonempty ∧ (∀ U ∈ B, U.Nonempty) ∧
    ∀ U ∈ B, ∀ V ∈ B, ∃ W ∈ B, W ⊆ U ∩ V

def FiniteIntersectionProperty {X : Type u} (A : Set (Set X)) : Prop :=
  ∀ C : Set (Set X), C ⊆ A → C.Finite → (⋂₀ C).Nonempty

def GeneratedFilter {X : Type u} (A : Set (Set X)) : Filter X :=
  Filter.generate A

def FilterFiner {X : Type u} (G F : Filter X) : Prop :=
  F.sets ⊆ G.sets

def ImageFilter {X : Type u} {Y : Type v} (f : X → Y) (F : Filter X) : Filter Y :=
  Filter.map f F

def FilterConverges {X : Type u} [t : TopologicalSpace X] (F : Filter X) (x : X) : Prop :=
  ∀ N : Set X, Neighborhood t x N → N ∈ F

def FilterClusters {X : Type u} [t : TopologicalSpace X] (F : Filter X) (x : X) : Prop :=
  ∀ U ∈ F, ∀ N : Set X, Neighborhood t x N → (U ∩ N).Nonempty

theorem proper_iff_empty_not_mem {X : Type u} (F : Filter X) :
    F.NeBot ↔ (∅ : Set X) ∉ F := by
  rw [neBot_iff, empty_mem_iff_bot]

theorem properFamily_iff_filter {X : Type u} (A : Set (Set X)) :
    ProperFamily A ↔ ∃! F : Filter X, F.sets = A ∧ F.NeBot := by
  constructor
  · rintro ⟨hne, hemp, hmono, hinter⟩
    let F : Filter X := {
      sets := A
      univ_sets := by
        obtain ⟨U, hU⟩ := hne
        exact hmono U hU univ (subset_univ U)
      sets_of_superset := fun hUV hVW => hmono _ hUV _ hVW
      inter_sets := fun hU hV => hinter _ hU _ hV }
    refine ⟨F, ⟨rfl, (proper_iff_empty_not_mem F).mpr hemp⟩, ?_⟩
    intro G hG
    exact Filter.filter_eq hG.1
  · rintro ⟨F, ⟨hFA, hF⟩, _⟩
    subst A
    let := hF
    exact ⟨⟨univ, univ_mem⟩, Filter.empty_notMem F,
      fun _ hU _ hUV => mem_of_superset hU hUV,
      fun _ hU _ hV => inter_mem hU hV⟩

theorem filter_finite_intersections {X : Type u} (F : Filter X)
    (C : Set (Set X)) (hC : C.Finite) (hCF : C ⊆ F.sets) : ⋂₀ C ∈ F :=
  (Filter.sInter_mem hC).mpr hCF

theorem finer_iff_le {X : Type u} (G F : Filter X) : FilterFiner G F ↔ G ≤ F :=
  Iff.rfl

theorem generated_mem {X : Type u} (A : Set (Set X)) (U : Set X) :
    U ∈ GeneratedFilter A ↔ ∃ C ⊆ A, C.Finite ∧ ⋂₀ C ⊆ U :=
  Filter.mem_generate_iff

theorem generated_contains {X : Type u} (A : Set (Set X)) :
    A ⊆ (GeneratedFilter A).sets := fun _ hU => Filter.mem_generate_of_mem hU

theorem generated_smallest {X : Type u} (A : Set (Set X)) (F : Filter X)
    (hA : A ⊆ F.sets) : FilterFiner F (GeneratedFilter A) :=
  Filter.le_generate_iff.mpr hA

/-- The library's general filter bases permit empty members. The extra
nonempty-member condition in the paper will supply properness below. -/
private def toFilterBasis {X : Type u} (B : Set (Set X)) (hB : FilterBase B) :
    FilterBasis X where
  sets := B
  nonempty := hB.1
  inter_sets := fun hU hV => hB.2.2 _ hU _ hV

theorem base_generated_mem {X : Type u} (B : Set (Set X)) (hB : FilterBase B)
    (U : Set X) : U ∈ GeneratedFilter B ↔ ∃ V ∈ B, V ⊆ U := by
  change U ∈ Filter.generate (toFilterBasis B hB).sets ↔ _
  rw [(toFilterBasis B hB).generate]
  rfl

theorem base_generates_proper {X : Type u} (B : Set (Set X)) (hB : FilterBase B) :
    (GeneratedFilter B).NeBot := by
  apply (proper_iff_empty_not_mem _).mpr
  intro h
  obtain ⟨V, hV, hVe⟩ := (base_generated_mem B hB ∅).mp h
  exact (hB.2.1 V hV).not_subset_empty hVe

theorem generated_proper_iff_fip {X : Type u} (A : Set (Set X)) :
    (GeneratedFilter A).NeBot ↔ FiniteIntersectionProperty A :=
  Filter.generate_neBot_iff

theorem fip_iff_contained_in_proper {X : Type u} (A : Set (Set X)) :
    FiniteIntersectionProperty A ↔ ∃ F : Filter X, F.NeBot ∧ A ⊆ F.sets := by
  constructor
  · intro hA
    exact ⟨GeneratedFilter A, (generated_proper_iff_fip A).mpr hA,
      generated_contains A⟩
  · rintro ⟨F, hF, hAF⟩ C hCA hC
    exact hF.nonempty_of_mem (filter_finite_intersections F C hC (hCA.trans hAF))

theorem no_proper_filter_on_empty {X : Type u} [IsEmpty X] :
    IsEmpty (ProperFilter X) := by
  refine ⟨fun F => ?_⟩
  exact F.2.ne (Filter.filter_eq_bot_of_isEmpty F.1)

theorem neighborhood_filter_proper {X : Type u} [TopologicalSpace X] (x : X) :
    (nhds x).NeBot := inferInstance

theorem neighborhood_filter_family {X : Type u} [t : TopologicalSpace X] (x : X) :
    (nhds x).sets = {N | Neighborhood t x N} := by
  ext N
  exact (neighborhood_iff_mem_nhds t x N).symm

theorem image_mem {X : Type u} {Y : Type v} (f : X → Y) (F : Filter X) (B : Set Y) :
    B ∈ ImageFilter f F ↔ f ⁻¹' B ∈ F := Iff.rfl

theorem image_proper {X : Type u} {Y : Type v} (f : X → Y) (F : Filter X) [F.NeBot] :
    (ImageFilter f F).NeBot := Filter.map_neBot

theorem image_generated_mem {X : Type u} {Y : Type v} (f : X → Y)
    (F : Filter X) (B : Set Y) :
    B ∈ ImageFilter f F ↔ ∃ A ∈ F, f '' A ⊆ B :=
  Filter.mem_map_iff_exists_image

theorem image_sets_base {X : Type u} {Y : Type v} (f : X → Y)
    (F : Filter X) [F.NeBot] :
    FilterBase ((fun A : Set X => f '' A) '' F.sets) := by
  refine ⟨⟨f '' univ, ⟨univ, univ_mem, rfl⟩⟩, ?_, ?_⟩
  · rintro _ ⟨A, hA, rfl⟩
    exact (Filter.nonempty_of_mem hA).image f
  · rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    exact ⟨f '' (A ∩ B), ⟨A ∩ B, inter_mem hA hB, rfl⟩, image_inter_subset _ _ _⟩

theorem image_eq_generated {X : Type u} {Y : Type v} (f : X → Y) (F : Filter X) :
    ImageFilter f F = GeneratedFilter ((fun A : Set X => f '' A) '' F.sets) := by
  apply le_antisymm
  · apply Filter.le_generate_iff.mpr
    rintro _ ⟨A, hA, rfl⟩
    exact Filter.image_mem_map hA
  · intro B hB
    obtain ⟨A, hA, hAB⟩ := (image_generated_mem f F B).mp hB
    exact mem_of_superset (generated_contains _ ⟨A, hA, rfl⟩) hAB

theorem converges_iff_le_nhds {X : Type u} [t : TopologicalSpace X]
    (F : Filter X) (x : X) : FilterConverges F x ↔ F ≤ nhds x := by
  simp only [FilterConverges, neighborhood_iff_mem_nhds]
  rfl

theorem clusters_iff_clusterPt {X : Type u} [t : TopologicalSpace X]
    (F : Filter X) (x : X) : FilterClusters F x ↔ ClusterPt x F := by
  simp only [FilterClusters, neighborhood_iff_mem_nhds]
  rw [clusterPt_iff_nonempty]
  constructor
  · intro h N hN U hU
    simpa only [inter_comm] using h U hU N hN
  · intro h U hU N hN
    simpa only [inter_comm] using h hN hU

theorem clusters_iff_closures {X : Type u} [TopologicalSpace X]
    (F : Filter X) (x : X) : FilterClusters F x ↔ x ∈ ⋂ U ∈ F, closure U := by
  rw [clusters_iff_clusterPt, clusterPt_iff_forall_mem_closure]
  simp only [mem_iInter]

theorem clusters_iff_finer_converges {X : Type u} [TopologicalSpace X]
    (F : Filter X) [F.NeBot] (x : X) :
    FilterClusters F x ↔ ∃ G : Filter X, G.NeBot ∧ FilterFiner G F ∧
      FilterConverges G x := by
  rw [clusters_iff_clusterPt]
  constructor
  · intro h
    exact ⟨nhds x ⊓ F, h, (finer_iff_le _ _).mpr inf_le_right,
      (converges_iff_le_nhds _ x).mpr inf_le_left⟩
  · rintro ⟨G, hG, hGF, hGx⟩
    exact (ClusterPt.of_le_nhds' ((converges_iff_le_nhds G x).mp hGx) hG).mono hGF

theorem closure_iff_proper_filter {X : Type u} [TopologicalSpace X]
    (A : Set X) (x : X) :
    x ∈ closure A ↔ ∃ F : Filter X, F.NeBot ∧ A ∈ F ∧ FilterConverges F x := by
  constructor
  · intro hx
    have h := mem_closure_iff_clusterPt.mp hx
    exact ⟨nhds x ⊓ Filter.principal A, h,
      Filter.mem_inf_of_right (Filter.mem_principal_self A),
      (converges_iff_le_nhds _ x).mpr inf_le_left⟩
  · rintro ⟨F, hF, hAF, hFx⟩
    apply mem_closure_iff_clusterPt.mpr
    exact (ClusterPt.of_le_nhds' ((converges_iff_le_nhds F x).mp hFx) hF).mono
      (Filter.le_principal_iff.mpr hAF)

theorem continuousAt_iff_nhds_image {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (x : X) :
    ContinuousAt f x ↔ FilterConverges (ImageFilter f (nhds x)) (f x) := by
  rw [converges_iff_le_nhds]
  rfl

theorem continuousAt_iff_filters {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (x : X) :
    ContinuousAt f x ↔ ∀ F : Filter X, F.NeBot → FilterConverges F x →
      FilterConverges (ImageFilter f F) (f x) := by
  constructor
  · intro hf F _ hFx
    apply (converges_iff_le_nhds _ _).mpr
    exact (Filter.map_mono ((converges_iff_le_nhds F x).mp hFx)).trans hf
  · intro h
    exact (continuousAt_iff_nhds_image f x).mpr
      (h (nhds x) inferInstance ((converges_iff_le_nhds _ x).mpr le_rfl))

end D10Topology.Ch04
