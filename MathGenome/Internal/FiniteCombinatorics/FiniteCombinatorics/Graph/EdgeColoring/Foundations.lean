import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.MultigraphFoundation

/-! Proper colorings of actual indexed edges, with the empty palette allowed.
Distinct edge colors prove existence; the natural infimum is therefore attained
for every finite graph. At a loopless vertex a proper coloring injects its
incident edge set into the palette, proving the maximum-degree lower bound.
The simple-graph specialization retains the same edge set and degrees. -/

universe u v
noncomputable section
namespace FiniteCombinatorics.Graph.EdgeColoring

abbrev Coloring : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.ColoringType :=
  Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.ColoringValue

abbrev Colorable : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.ColorableType :=
  Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.ColorableValue

abbrev chromaticIndex : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.chromaticIndexType :=
  Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.chromaticIndexValue

abbrev maximumDegree : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.maximumDegreeType :=
  Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.maximumDegreeValue

abbrev SimpleColoring : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.SimpleColoringType :=
  Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.SimpleColoringValue

abbrev SimpleColorable : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.SimpleColorableType :=
  Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.SimpleColorableValue

abbrev simpleChromaticIndex : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.simpleChromaticIndexType :=
  Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.simpleChromaticIndexValue

abbrev simpleMaximumDegree : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.simpleMaximumDegreeType :=
  Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.simpleMaximumDegreeValue

theorem colorable_distinct_edges : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.colorable_distinct_edgesType := by
  intro α β G h
  let : Finite (Multigraph.Edge G) := Multigraph.finite_edges G h
  let := Fintype.ofFinite (Multigraph.Edge G)
  let e : Multigraph.Edge G ≃ Fin (Nat.card (Multigraph.Edge G)) :=
    Fintype.equivFinOfCardEq Nat.card_eq_fintype_card.symm
  exact ⟨⟨e, fun a b hab _ heq => hab (e.injective heq)⟩⟩

theorem colorable_exists : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.colorable_existsType := by
  intro α β G h
  exact ⟨_, colorable_distinct_edges G h⟩

theorem colorable_mono : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.colorable_monoType := by
  intro α β G k l h ⟨c, hc⟩
  refine ⟨⟨fun e => Fin.castLE h (c e), ?_⟩⟩
  intro e f hef hx heq
  apply hc e f hef hx
  exact Fin.ext (congrArg (fun a : Fin l => a.val) heq)

theorem chromaticIndex_attained : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.chromaticIndex_attainedType := by
  intro α β G h
  exact csInf_mem (colorable_exists G h)

theorem chromaticIndex_le : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.chromaticIndex_leType := by
  intro α β G k h
  exact csInf_le' h

theorem colorable_iff_chromaticIndex_le : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.colorable_iff_chromaticIndex_leType := by
  intro α β G h k
  exact ⟨chromaticIndex_le G, fun hk =>
    colorable_mono G hk (chromaticIndex_attained G h)⟩

theorem colorable_zero_iff : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.colorable_zero_iffType := by
  intro α β G
  constructor
  · rintro ⟨c⟩
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro e he
    exact Fin.elim0 (c.val ⟨e, he⟩)
  · intro h
    let : IsEmpty (Multigraph.Edge G) := ⟨fun e => by
      have he := e.property
      simp only [h, Set.mem_empty_iff_false] at he⟩
    exact ⟨⟨isEmptyElim, fun e => isEmptyElim e⟩⟩

theorem chromaticIndex_zero_iff : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.chromaticIndex_zero_iffType := by
  intro α β G h
  constructor
  · intro hz
    apply (colorable_zero_iff G).mp
    simpa only [hz] using chromaticIndex_attained G h
  · intro he
    exact Nat.eq_zero_of_le_zero (chromaticIndex_le G ((colorable_zero_iff G).mpr he))

theorem degree_le_colors : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.degree_le_colorsType := by
  intro α β G _ k ⟨c, hc⟩ x
  rw [Multigraph.degree_loopless]
  let f : G.incidenceSet x → Fin k := fun e => c ⟨e.val, e.property.edge_mem⟩
  have hf : Function.Injective f := by
    intro e f' heq
    by_contra hne
    have hne' : (⟨e.val, e.property.edge_mem⟩ : Multigraph.Edge G) ≠
        ⟨f'.val, f'.property.edge_mem⟩ := by
      intro h
      exact hne (Subtype.ext (congrArg (fun a : Multigraph.Edge G => a.val) h))
    exact hc _ _ hne' ⟨x, e.property, f'.property⟩ heq
  simpa using Nat.card_le_card_of_injective f hf

theorem maximumDegree_le_colors : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.maximumDegree_le_colorsType := by
  intro α β G _ h k hc
  exact Finset.sup_le (fun x _ => degree_le_colors G hc x)

theorem maximumDegree_le_chromaticIndex : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.maximumDegree_le_chromaticIndexType := by
  intro α β G _ h
  exact maximumDegree_le_colors G h (chromaticIndex_attained G h)

theorem degree_le_maximumDegree : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.degree_le_maximumDegreeType := by
  intro α β G h x
  classical
  by_cases hx : x ∈ G.vertexSet
  · exact Finset.le_sup (h.1.mem_toFinset.mpr hx)
  · rw [Multigraph.degree_outside G x hx]
    exact Nat.zero_le _

theorem maximumDegree_empty_vertices : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.maximumDegree_empty_verticesType := by
  intro α β G h he
  change h.1.toFinset.sup (Multigraph.degree G) = 0
  rw [h.1.toFinset_eq_empty.mpr he]
  rfl

theorem simple_coloring_iff : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.simple_coloring_iffType := by
  intro V G k c
  constructor
  · intro hc
    refine ⟨⟨c, ?_⟩, rfl⟩
    intro e f hef hx
    obtain ⟨x, he, hf⟩ := hx
    exact hc e f hef ⟨x, (Multigraph.ofSimpleGraph_incidence G e.val x).mp he,
      (Multigraph.ofSimpleGraph_incidence G f.val x).mp hf⟩
  · rintro ⟨C, rfl⟩ e f hef ⟨x, he, hf⟩
    exact C.property e f hef ⟨x,
      (Multigraph.ofSimpleGraph_incidence G e.val x).mpr he,
      (Multigraph.ofSimpleGraph_incidence G f.val x).mpr hf⟩

theorem simple_colorable_iff : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.simple_colorable_iffType := by
  intro V G k
  rfl

theorem simple_colorable_distinct_edges : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.simple_colorable_distinct_edgesType := by
  intro V _ G
  exact colorable_distinct_edges (Multigraph.ofSimpleGraph G) (Multigraph.ofSimpleGraph_finite G)

theorem simple_chromaticIndex_attained : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.simple_chromaticIndex_attainedType := by
  intro V _ G
  exact chromaticIndex_attained (Multigraph.ofSimpleGraph G) (Multigraph.ofSimpleGraph_finite G)

theorem simple_colorable_iff_chromaticIndex_le : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.simple_colorable_iff_chromaticIndex_leType := by
  intro V _ G k
  exact colorable_iff_chromaticIndex_le (Multigraph.ofSimpleGraph G)
    (Multigraph.ofSimpleGraph_finite G) k

theorem simple_chromaticIndex_zero_iff : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.simple_chromaticIndex_zero_iffType := by
  intro V _ G
  exact chromaticIndex_zero_iff (Multigraph.ofSimpleGraph G) (Multigraph.ofSimpleGraph_finite G)

theorem maximumDegree_ofSimpleGraph : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.maximumDegree_ofSimpleGraphType := by
  intro V _ G h
  classical
  change h.1.toFinset.sup _ = (Set.toFinite (Set.univ : Set V)).toFinset.sup _
  have hs : h.1.toFinset = (Set.toFinite (Set.univ : Set V)).toFinset := by
    ext x
    simp only [Set.Finite.mem_toFinset]
    rfl
  rw [hs]
  apply Finset.sup_congr rfl
  intro x _
  exact Multigraph.degree_ofSimpleGraph G x

theorem simple_degree_le_chromaticIndex : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.simple_degree_le_chromaticIndexType := by
  intro V _ G x
  have h := degree_le_colors (Multigraph.ofSimpleGraph G)
    (simple_chromaticIndex_attained G) x
  rw [Multigraph.degree_ofSimpleGraph] at h
  exact h

theorem simple_maximumDegree_le_chromaticIndex : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.simple_maximumDegree_le_chromaticIndexType := by
  intro V _ G
  exact Finset.sup_le (fun x _ => simple_degree_le_chromaticIndex G x)

theorem simple_maximumDegree_empty : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.simple_maximumDegree_emptyType := by
  intro V _ _ G
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro x _
  exact isEmptyElim x

theorem simple_maximumDegree_mathlib : Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations.simple_maximumDegree_mathlibType := by
  intro V _ G _
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro x _
    simpa only [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree] using G.degree_le_maxDegree x
  · apply G.maxDegree_le_of_forall_degree_le
    intro x
    have h : Nat.card (G.neighborSet x) ≤ simpleMaximumDegree G :=
      Finset.le_sup (f := fun y => Nat.card (G.neighborSet y))
        ((Set.toFinite (Set.univ : Set V)).mem_toFinset.mpr (Set.mem_univ x))
    simpa only [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree] using h

end FiniteCombinatorics.Graph.EdgeColoring
