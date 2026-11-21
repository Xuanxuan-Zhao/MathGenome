import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.Models
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.GraphicRank

/-! Labelled graphic interfaces for paper.tex W46–W48. Only the actual vertex
and edge sets are finite. Loops are one-cycles, and parallel pairs are two-cycles.
All shadows retain the full vertex set, including isolates. -/
namespace Specs.P205.Matroids.Graphic
open _root_.FiniteCombinatorics.Matroid.Graphic
open Specs.FiniteCombinatorics.Graph.MultigraphFoundation
open Specs.P205.Matroids
open scoped BigOperators
noncomputable section
set_option linter.checkUnivs false
set_option linter.unusedVariables false
universe u v

def IsFiniteType := ∀ {α : Type u} {β : Type v}, Graph α β → Prop

def IsFiniteValue : IsFiniteType.{u, v} :=
  fun G => G.vertexSet.Finite ∧ G.edgeSet.Finite

def graphicMatroidType := ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G), Matroid β

def graphicMatroidValue : graphicMatroidType.{u, v} :=
  fun G hG => incidenceMatroid G hG ℚ {
    tail := fun e => (G.exists_isLink_of_mem_edgeSet e.property).choose
    head := fun e => (G.exists_isLink_of_mem_edgeSet e.property).choose_spec.choose
    link := fun e => (G.exists_isLink_of_mem_edgeSet e.property).choose_spec.choose_spec }

instance graphicMatroidValue_finite {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G) : (graphicMatroidValue G hG).Finite := by
  exact ⟨hG.2⟩

def ForestType := ∀ {α : Type u} {β : Type v}, Graph α β → Set β → Prop

def ForestValue : ForestType.{u, v} :=
  fun G A => _root_.FiniteCombinatorics.Matroid.Graphic.Forest G A

def SpanningForestType := ∀ {α : Type u} {β : Type v}, Graph α β → Set β → Prop

def SpanningForestValue : SpanningForestType.{u, v} :=
  fun G B => _root_.FiniteCombinatorics.Matroid.Graphic.SpanningForest G B G.edgeSet

def SpanningTreeType := ∀ {α : Type u} {β : Type v}, Graph α β → Set β → Prop

def SpanningTreeValue : SpanningTreeType.{u, v} :=
  fun G B => B ⊆ G.edgeSet ∧ (G.restrict B).Simple ∧ (spanningShadow G B).IsTree

def componentCountType := ∀ {α : Type u} {β : Type v}, Graph α β → Set β → ℕ

def componentCountValue : componentCountType.{u, v} :=
  fun G A => spanningComponentCount G A

def inducedEdgesType := ∀ {α : Type u} {β : Type v}, Graph α β → Set α → Set β

def inducedEdgesValue : inducedEdgesType.{u, v} :=
  fun G S => {e | ∃ x ∈ S, ∃ y ∈ S, G.IsLink e x y}

def edgeWeightType := ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G), (G.edgeSet → ℝ) → Set β → ℝ

def edgeWeightValue : edgeWeightType.{u, v} :=
  fun G hG w B => by
  classical
  letI := hG.2.fintype
  exact ∑ e : G.edgeSet, if e.val ∈ B then w e else 0

def MinimumSpanningForestType := ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G), (G.edgeSet → ℝ) → Set β → Prop

def MinimumSpanningForestValue : MinimumSpanningForestType.{u, v} :=
  fun G hG w B => SpanningForestValue G B ∧ ∀ D, SpanningForestValue G D → edgeWeightValue G hG w B ≤ edgeWeightValue G hG w D

def UniqueMinimumSpanningForestType := ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G), (G.edgeSet → ℝ) → Set β → Prop

def UniqueMinimumSpanningForestValue : UniqueMinimumSpanningForestType.{u, v} :=
  fun G hG w B => MinimumSpanningForestValue G hG w B ∧ ∀ D, MinimumSpanningForestValue G hG w D → D = B

def MinimumSpanningTreeType := ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G), (G.edgeSet → ℝ) → Set β → Prop

def MinimumSpanningTreeValue : MinimumSpanningTreeType.{u, v} :=
  fun G hG w B => SpanningTreeValue G B ∧ ∀ D, SpanningTreeValue G D → edgeWeightValue G hG w B ≤ edgeWeightValue G hG w D

def UniqueMinimumSpanningTreeType := ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G), (G.edgeSet → ℝ) → Set β → Prop

def UniqueMinimumSpanningTreeValue : UniqueMinimumSpanningTreeType.{u, v} :=
  fun G hG w B => MinimumSpanningTreeValue G hG w B ∧ ∀ D, MinimumSpanningTreeValue G hG w D → D = B

def ground_eq : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G), (graphicMatroidValue G hG).E = G.edgeSet

def indep_iff_forest : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G), ∀ A, (graphicMatroidValue G hG).Indep A ↔ ForestValue G A

def basis_iff_spanningForest : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G), ∀ B A, A ⊆ G.edgeSet → ((graphicMatroidValue G hG).IsBasis B A ↔ _root_.FiniteCombinatorics.Matroid.Graphic.SpanningForest G B A)

def base_iff_spanningForest : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G), ∀ B, (graphicMatroidValue G hG).IsBase B ↔ SpanningForestValue G B

def base_iff_component_trees : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G), ∀ B, (graphicMatroidValue G hG).IsBase B ↔ B ⊆ G.edgeSet ∧ (G.restrict B).Simple ∧ ∀ C : (spanningShadow G G.edgeSet).ConnectedComponent, ((spanningShadow G B).induce C.supp).IsTree

def rank_eq_vertices_sub_components : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G), ∀ A, A ⊆ G.edgeSet → (rankValue (graphicMatroidValue G hG) A : ℤ) = (G.vertexSet.ncard : ℤ) - (componentCountValue G A : ℤ)

def rank_add_components : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G), ∀ A, A ⊆ G.edgeSet → rankValue (graphicMatroidValue G hG) A + componentCountValue G A = G.vertexSet.ncard

def total_rank : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G), (rankValue (graphicMatroidValue G hG) G.edgeSet : ℤ) = (G.vertexSet.ncard : ℤ) - (Nat.card G.toSimpleGraph.ConnectedComponent : ℤ)

def spanningShadow_self : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β), spanningShadow G G.edgeSet = G.toSimpleGraph

def connected_spanningForest_iff_tree : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β), G.toSimpleGraph.Connected → ∀ B, SpanningForestValue G B ↔ SpanningTreeValue G B

def connected_base_iff_tree : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G), G.toSimpleGraph.Connected → ∀ B, (graphicMatroidValue G hG).IsBase B ↔ SpanningTreeValue G B

def connected_components_one : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β), G.toSimpleGraph.Connected → componentCountValue G G.edgeSet = 1

def connected_rank : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G), G.toSimpleGraph.Connected → (rankValue (graphicMatroidValue G hG) G.edgeSet : ℤ) = (G.vertexSet.ncard : ℤ) - 1

def spanningForest_exists : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G), ∃ B, SpanningForestValue G B

def spanningTree_exists : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G), G.toSimpleGraph.Connected → ∃ B, SpanningTreeValue G B

def inducedEdges_subset : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β), ∀ S, inducedEdgesValue G S ⊆ G.edgeSet

def mem_inducedEdges_iff : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β), ∀ S e x y, G.IsLink e x y → (e ∈ inducedEdgesValue G S ↔ x ∈ S ∧ y ∈ S)

def weight_eq_subsetSum : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G), ∀ (w : G.edgeSet → ℝ) B, edgeWeightValue G hG w B = subsetSumValue (graphicMatroidValue G hG) w B

def minimumSpanningForest_iff_base : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G), ∀ (w : G.edgeSet → ℝ) B, MinimumSpanningForestValue G hG w B ↔ (graphicMatroidValue G hG).IsBase B ∧ ∀ D, (graphicMatroidValue G hG).IsBase D → edgeWeightValue G hG w B ≤ edgeWeightValue G hG w D

def connected_minimum_iff : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G), G.toSimpleGraph.Connected → ∀ w B, MinimumSpanningForestValue G hG w B ↔ MinimumSpanningTreeValue G hG w B

def connected_unique_minimum_iff : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G), G.toSimpleGraph.Connected → ∀ w B, UniqueMinimumSpanningForestValue G hG w B ↔ UniqueMinimumSpanningTreeValue G hG w B

def empty_vertices_spanningForest : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G), G.vertexSet = ∅ → ∀ B, SpanningForestValue G B ↔ B = ∅

end
end Specs.P205.Matroids.Graphic
