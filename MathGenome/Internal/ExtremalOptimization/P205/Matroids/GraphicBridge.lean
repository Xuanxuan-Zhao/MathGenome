import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.GraphicBridge
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.GraphicRank
import MathGenome.Internal.ExtremalOptimization.P205.Matroids.Models
import Lean.Elab.Tactic.Omega

namespace P205.Matroids.Graphic
open _root_.FiniteCombinatorics.Matroid.Graphic
open Specs.P205.Matroids.Graphic
noncomputable section
set_option linter.checkUnivs false
set_option linter.unusedVariables false
universe u v

def IsFinite : IsFiniteType.{u, v} := @IsFiniteValue.{u, v}

def graphicMatroid : graphicMatroidType.{u, v} := @graphicMatroidValue.{u, v}

instance graphicMatroid_finite {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFinite G) : (graphicMatroid G hG).Finite := ⟨hG.2⟩

def Forest : ForestType.{u, v} := @ForestValue.{u, v}

def SpanningForest : SpanningForestType.{u, v} := @SpanningForestValue.{u, v}

def SpanningTree : SpanningTreeType.{u, v} := @SpanningTreeValue.{u, v}

def componentCount : componentCountType.{u, v} := @componentCountValue.{u, v}

def inducedEdges : inducedEdgesType.{u, v} := @inducedEdgesValue.{u, v}

def edgeWeight : edgeWeightType.{u, v} := @edgeWeightValue.{u, v}

def MinimumSpanningForest : MinimumSpanningForestType.{u, v} := @MinimumSpanningForestValue.{u, v}

def UniqueMinimumSpanningForest : UniqueMinimumSpanningForestType.{u, v} := @UniqueMinimumSpanningForestValue.{u, v}

def MinimumSpanningTree : MinimumSpanningTreeType.{u, v} := @MinimumSpanningTreeValue.{u, v}

def UniqueMinimumSpanningTree : UniqueMinimumSpanningTreeType.{u, v} := @UniqueMinimumSpanningTreeValue.{u, v}

theorem ground_eq : Specs.P205.Matroids.Graphic.ground_eq.{u, v} := by
  intro α β G hG
  rfl

theorem indep_iff_forest : Specs.P205.Matroids.Graphic.indep_iff_forest.{u, v} := by
  intro α β G hG A
  exact incidenceMatroid_indep G hG ℚ _ A

theorem basis_iff_spanningForest : Specs.P205.Matroids.Graphic.basis_iff_spanningForest.{u, v} := by
  intro α β G hG B A hA
  exact _root_.FiniteCombinatorics.Matroid.Graphic.basis_iff_spanningForest G hG ℚ _ B A hA

theorem base_iff_spanningForest : Specs.P205.Matroids.Graphic.base_iff_spanningForest.{u, v} := by
  intro α β G hG B
  exact _root_.FiniteCombinatorics.Matroid.Graphic.base_iff_spanningForest G hG ℚ _ B

theorem base_iff_component_trees : Specs.P205.Matroids.Graphic.base_iff_component_trees.{u, v} := by
  intro α β G hG B
  exact _root_.FiniteCombinatorics.Matroid.Graphic.base_iff_component_trees G hG ℚ _ B

theorem rank_eq_vertices_sub_components : Specs.P205.Matroids.Graphic.rank_eq_vertices_sub_components.{u, v} := by
  intro α β G hG A hA
  exact _root_.FiniteCombinatorics.Matroid.Graphic.rank_eq_vertices_sub_components G hG ℚ _ A hA

theorem rank_add_components : Specs.P205.Matroids.Graphic.rank_add_components.{u, v} := by
  intro α β G hG A hA
  have h := rank_eq_vertices_sub_components G hG A hA
  omega

theorem total_rank : Specs.P205.Matroids.Graphic.total_rank.{u, v} := by
  intro α β G hG
  exact _root_.FiniteCombinatorics.Matroid.Graphic.total_rank G hG ℚ _

theorem spanningShadow_self : Specs.P205.Matroids.Graphic.spanningShadow_self.{u, v} := by
  intro α β G
  ext x y
  change (x ≠ y ∧ ∃ e, e ∈ G.edgeSet ∧ G.IsLink e x.val y.val) ↔
    (x ≠ y ∧ ∃ e, G.IsLink e x.val y.val)
  constructor
  · rintro ⟨hne, e, _, hl⟩
    exact ⟨hne, e, hl⟩
  · rintro ⟨hne, e, hl⟩
    exact ⟨hne, e, hl.edge_mem, hl⟩

theorem connected_spanningForest_iff_tree : Specs.P205.Matroids.Graphic.connected_spanningForest_iff_tree.{u, v} := by
  intro α β G hC B
  constructor
  · intro hB
    have hc : (spanningShadow G B).Connected := {
      preconnected := fun x y => hB.2.2 x y (by
        simpa only [spanningShadow_self G] using hC x y)
      nonempty := hC.nonempty }
    exact ⟨hB.1, hB.2.1.restrict_simple G, hc, hB.2.1.shadow_acyclic G⟩
  · rintro ⟨hBE, hs, ht⟩
    let : (G.restrict B).Simple := hs
    have hf : _root_.FiniteCombinatorics.Matroid.Graphic.Forest G B := by
      apply (forest_restrict G B).mp
      have he : (G.restrict B).edgeSet = B := Set.inter_eq_right.mpr hBE
      simpa only [he] using forest_of_simple_shadow (G.restrict B) ht.isAcyclic
    exact ⟨hBE, hf, fun x y _ => ht.connected x y⟩

theorem connected_base_iff_tree : Specs.P205.Matroids.Graphic.connected_base_iff_tree.{u, v} := by
  intro α β G hG hC B
  exact (base_iff_spanningForest G hG B).trans (connected_spanningForest_iff_tree G hC B)

theorem connected_components_one : Specs.P205.Matroids.Graphic.connected_components_one.{u, v} := by
  intro α β G hC
  change Nat.card (spanningShadow G G.edgeSet).ConnectedComponent = 1
  rw [spanningShadow_self G]
  let := hC.nonempty
  apply Nat.card_eq_one_iff_unique.mpr
  refine ⟨⟨?_⟩, inferInstance⟩
  intro c d
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h x =>
    induction d using SimpleGraph.ConnectedComponent.ind with
    | h y => exact SimpleGraph.ConnectedComponent.sound (hC x y)

theorem connected_rank : Specs.P205.Matroids.Graphic.connected_rank.{u, v} := by
  intro α β G hG hC
  have h := rank_eq_vertices_sub_components G hG G.edgeSet Set.Subset.rfl
  rw [connected_components_one G hC] at h
  exact h

theorem spanningForest_exists : Specs.P205.Matroids.Graphic.spanningForest_exists.{u, v} := by
  intro α β G hG
  obtain ⟨B, hB⟩ := (graphicMatroidValue G hG).exists_isBase
  exact ⟨B, (base_iff_spanningForest G hG B).mp hB⟩

theorem spanningTree_exists : Specs.P205.Matroids.Graphic.spanningTree_exists.{u, v} := by
  intro α β G hG hC
  obtain ⟨B, hB⟩ := spanningForest_exists G hG
  exact ⟨B, (connected_spanningForest_iff_tree G hC B).mp hB⟩

theorem inducedEdges_subset : Specs.P205.Matroids.Graphic.inducedEdges_subset.{u, v} := by
  intro α β G S e he
  obtain ⟨x, _, y, _, h⟩ := he
  exact h.edge_mem

theorem mem_inducedEdges_iff : Specs.P205.Matroids.Graphic.mem_inducedEdges_iff.{u, v} := by
  intro α β G S e x y h
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    rcases h.eq_and_eq_or_eq_and_eq hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨ha, hb⟩
    · exact ⟨hb, ha⟩
  · rintro ⟨hx, hy⟩
    exact ⟨x, hx, y, hy, h⟩

theorem weight_eq_subsetSum : Specs.P205.Matroids.Graphic.weight_eq_subsetSum.{u, v} := by
  intro α β G hG w B
  rfl

theorem minimumSpanningForest_iff_base : Specs.P205.Matroids.Graphic.minimumSpanningForest_iff_base.{u, v} := by
  intro α β G hG w B
  simp only [MinimumSpanningForestValue, base_iff_spanningForest G hG]

theorem connected_minimum_iff : Specs.P205.Matroids.Graphic.connected_minimum_iff.{u, v} := by
  intro α β G hG hC w B
  simp only [MinimumSpanningForestValue, MinimumSpanningTreeValue,
    connected_spanningForest_iff_tree G hC]

theorem connected_unique_minimum_iff : Specs.P205.Matroids.Graphic.connected_unique_minimum_iff.{u, v} := by
  intro α β G hG hC w B
  simp only [UniqueMinimumSpanningForestValue, UniqueMinimumSpanningTreeValue,
    connected_minimum_iff G hG hC]

theorem empty_vertices_spanningForest : Specs.P205.Matroids.Graphic.empty_vertices_spanningForest.{u, v} := by
  intro α β G hG hV B
  have hE : G.edgeSet = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨x, y, h⟩ := G.exists_isLink_of_mem_edgeSet he
    simpa [hV] using h.left_mem
  rw [← base_iff_spanningForest G hG B]
  exact _root_.P205.Matroids.empty_ground_base (graphicMatroidValue G hG) hE B

end
end P205.Matroids.Graphic
