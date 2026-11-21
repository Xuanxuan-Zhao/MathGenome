import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.CompactnessExamples
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.Compactness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.ElementaryTopologies
import MathGenome.Internal.PointSetTopology.D10Topology.Ch04.ProperFilters

/-! The examples of paper.tex d10:05:cautions, with the canonical topologies
and the established open-cover and proper-filter interfaces. -/

open Set Filter
open scoped Topology
universe u

namespace D10Topology.Ch05
open D10Topology.Ch01 D10Topology.Ch04

theorem finite_space_compact (X : Type u) [TopologicalSpace X] [Finite X] :
    CoverCompact X :=
  (coverCompact_iff_compactSpace X).mpr inferInstance

theorem indiscrete_space_compact (X : Type u) :
    @CoverCompact X (indiscrete X) := by
  let := indiscrete X
  exact (coverCompact_iff_compactSpace X).mpr inferInstance

theorem discrete_singleton_cover (X : Type u) [Infinite X] :
    (∀ U ∈ Set.range (fun x : X => ({x} : Set X)), IsOpen[discrete X] U) ∧
    (univ : Set X) ⊆ ⋃₀ Set.range (fun x : X => ({x} : Set X)) ∧
    ∀ V : Set (Set X), V ⊆ Set.range (fun x : X => ({x} : Set X)) →
      V.Finite → ¬ (univ : Set X) ⊆ ⋃₀ V := by
  refine ⟨fun _ _ => trivial, ?_, ?_⟩
  · intro x _
    exact mem_sUnion.mpr ⟨{x}, ⟨x, rfl⟩, mem_singleton x⟩
  · intro V hV hfin hcover
    have hfinite : (⋃₀ V).Finite := hfin.sUnion (by
      intro U hU
      obtain ⟨x, rfl⟩ := hV hU
      exact finite_singleton x)
    exact Set.infinite_univ (hfinite.subset hcover)

theorem infinite_discrete_not_compact (X : Type u) [Infinite X] :
    ¬ @CoverCompact X (discrete X) := by
  intro h
  obtain ⟨hopen, hcover, hno⟩ := discrete_singleton_cover X
  obtain ⟨V, hV, hfin, hcov⟩ := h _ hopen hcover
  exact hno V hV hfin hcov

/-- Remove one nonempty open cover member. The remaining set is finite,
so its compactness provides finitely many more members of the same cover. -/
theorem cofinite_subspace_compact (X : Type u) (K : Set X) :
    @SubspaceCompact X (cofiniteTopology X) K := by
  classical
  let := cofiniteTopology X
  apply (subspaceCompact_iff_ambient_open_cover K).mpr
  intro U hU hcover
  by_cases hK : K = ∅
  · subst K
    exact ⟨∅, empty_subset _, finite_empty, empty_subset _⟩
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hK
  obtain ⟨O, hOU, hxO⟩ := mem_sUnion.mp (hcover hx)
  have hOc : Oᶜ.Finite := by
    rcases (cofinite_opens X O).mp (hU O hOU) with he | hf
    · exact False.elim (by simp [he] at hxO)
    · exact hf
  have hrem : (K \ O).Finite := hOc.subset (by intro y hy; exact hy.2)
  have hremcover : K \ O ⊆ ⋃₀ U := fun _ hy => hcover hy.1
  obtain ⟨V, hVU, hV, hremV⟩ :=
    (ambientCoverCompact_iff_isCompact (K \ O)).mpr hrem.isCompact U hU hremcover
  refine ⟨insert O V, insert_subset hOU hVU, hV.insert O, ?_⟩
  intro y hy
  by_cases hyO : y ∈ O
  · exact mem_sUnion.mpr ⟨O, mem_insert O V, hyO⟩
  · obtain ⟨W, hWV, hyW⟩ := mem_sUnion.mp (hremV ⟨hy, hyO⟩)
    exact mem_sUnion.mpr ⟨W, mem_insert_of_mem O hWV, hyW⟩

theorem cofinite_space_compact (X : Type u) :
    @CoverCompact X (cofiniteTopology X) := by
  let := cofiniteTopology X
  apply (coverCompact_iff_isCompact_univ X).mpr
  exact (subspaceCompact_iff_isCompact univ).mp (cofinite_subspace_compact X univ)

theorem cofinite_infinite_proper_compact_nonclosed (X : Type u) [Infinite X]
    (A : Set X) (hA : A.Infinite) (hproper : A ≠ univ) :
    @SubspaceCompact X (cofiniteTopology X) A ∧ ¬ IsClosed[cofiniteTopology X] A := by
  refine ⟨cofinite_subspace_compact X A, ?_⟩
  intro hclosed
  exact ((cofinite_closed X A).mp hclosed).elim hA hproper

theorem indiscrete_filter_converges (X : Type u) (F : ProperFilter X) (x : X) :
    @FilterConverges X (indiscrete X) F.val x := by
  intro N hN
  obtain ⟨O, hO, hxO, hON⟩ := hN
  have heq : O = univ := by
    rcases (TopologicalSpace.isOpen_top_iff O).mp hO with he | he
    · exact False.elim (by simp [he] at hxO)
    · exact he
  exact Filter.mem_of_superset Filter.univ_mem (heq ▸ hON)

theorem two_point_indiscrete_filter_limits (F : ProperFilter Bool) :
    @FilterConverges Bool (indiscrete Bool) F.val false ∧
      @FilterConverges Bool (indiscrete Bool) F.val true :=
  ⟨indiscrete_filter_converges Bool F false, indiscrete_filter_converges Bool F true⟩

end D10Topology.Ch05
