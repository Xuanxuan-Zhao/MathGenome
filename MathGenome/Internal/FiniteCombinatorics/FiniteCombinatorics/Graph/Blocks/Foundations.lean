import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Trees.ForestsBridges
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Blocks.Foundations

/-! Vertex deletion, cut vertices, 2-connectivity, and blocks, as defined before W38.
Subgraph inclusion retains both vertex and edge data. The global incidence graph
is restricted to a component for the later componentwise block–cut tree theorem. -/

universe u
noncomputable section
namespace FiniteCombinatorics.Graph.Blocks
open FiniteCombinatorics.Graph.Trees

/-- Delete the vertex, with all incident edges; the remaining vertex type excludes it. -/
abbrev deleteVertex : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.deleteVertexType.{u} :=
  fun {_} _ G v => G.induce {w | w ≠ v}

/-- Delete v inside its original connected component, excluding all other components. -/
abbrev componentDeleteVertex : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.componentDeleteVertexType.{u} :=
  fun {_} _ G v => G.induce {w | G.Reachable v w ∧ w ≠ v}

/-- A cut vertex of its own component, including for a disconnected ambient graph. -/
abbrev CutVertex : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.CutVertexType.{u} :=
  fun {_} _ G v => 2 ≤ componentCount (componentDeleteVertex G v)

/-- The source convention excludes graphs on fewer than three vertices. -/
abbrev TwoConnected : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.TwoConnectedType.{u} :=
  fun {V} _ G => 3 ≤ Nat.card V ∧ G.Connected ∧
    ∀ v : V, (deleteVertex G v).Connected

/-- Maximal under inclusion of vertices and edges among all 2-connected subgraphs. -/
abbrev MaximalTwoConnectedSubgraph : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.MaximalTwoConnectedSubgraphType.{u} :=
  fun {_} _ G H => TwoConnected H.coe ∧
    ∀ K : G.Subgraph, H ≤ K → TwoConnected K.coe → K = H

/-- Exactly one bridge edge and its two endpoints; no additional isolated vertices. -/
abbrev BridgeBlock : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.BridgeBlockType.{u} :=
  fun {V} _ G H => ∃ (a b : V) (hab : G.Adj a b),
    Bridge G s(a, b) ∧ H = G.subgraphOfAdj hab

/-- The singleton subgraph at an isolated vertex of the ambient graph. -/
abbrev IsolatedBlock : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.IsolatedBlockType.{u} :=
  fun {V} _ G H => ∃ v : V, G.IsIsolated v ∧ H = G.singletonSubgraph v

/-- The three kinds of block in the paragraph preceding W38. -/
abbrev IsBlock : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.IsBlockType.{u} :=
  fun {_} _ G H => MaximalTwoConnectedSubgraph G H ∨
    BridgeBlock G H ∨ IsolatedBlock G H

/-- Blocks are actual subgraphs, identified by their vertices and edges. -/
abbrev Block : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.BlockType.{u} :=
  fun {_} _ G => {H : G.Subgraph // IsBlock G H}

/-- Separate block and cut-vertex nodes. All blocks, including isolated singletons, are retained. -/
abbrev BlockCutNode : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.BlockCutNodeType.{u} :=
  fun {V} _ G => Block G ⊕ {v : V // CutVertex G v}

/-- The bipartite incidence graph, with adjacency precisely vertex membership in a block. -/
abbrev blockCutGraph : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.blockCutGraphType.{u} :=
  fun {_} _ G => {
    Adj := fun x y => match x, y with
      | .inl B, .inr v => v.val ∈ B.val.verts
      | .inr v, .inl B => v.val ∈ B.val.verts
      | _, _ => False
    symm := ⟨by intro x y h; cases x <;> cases y <;> exact h⟩
    loopless := ⟨by intro x; cases x <;> exact not_false⟩ }

/-- The nodes associated with one original connected component. -/
abbrev componentNodes : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.componentNodesType.{u} :=
  fun {_} _ _G c x => match x with
    | .inl B => B.val.verts ⊆ c.supp
    | .inr v => v.val ∈ c.supp

/-- The componentwise block–cut incidence graph used in the statement of W38. -/
abbrev componentBlockCutGraph : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.componentBlockCutGraphType.{u} :=
  fun {_} _ G c => (blockCutGraph G).induce (componentNodes G c)

theorem deleteVertex_adjacency : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.deleteVertex_adjacencyType := by intro V _ G v a b; rfl

theorem componentDeleteVertex_adjacency : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.componentDeleteVertex_adjacencyType := by intro V _ G v a b; rfl

theorem cutVertex_iff : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.cutVertex_iffType := by intro V _ G v; rfl

theorem twoConnected_iff : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.twoConnected_iffType := by intro V _ G; rfl

theorem isBlock_iff : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.isBlock_iffType := by intro V _ G H; rfl

theorem blockCutGraph_adjacency : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.blockCutGraph_adjacencyType := by intro V _ G B v; rfl

theorem blockCutGraph_bipartite : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.blockCutGraph_bipartiteType := by intro V _ G; exact ⟨fun _ _ h => h, fun _ _ h => h⟩

theorem isolated_isBlock : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.isolated_isBlockType := by intro V _ G v hv; exact Or.inr (Or.inr ⟨v, hv, rfl⟩)

theorem isolated_not_cutVertex : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.isolated_not_cutVertexType := by
  intro V _ G v hv
  have hempty : IsEmpty {w : V // G.Reachable v w ∧ w ≠ v} := by
    refine ⟨fun w => ?_⟩
    exact SimpleGraph.not_reachable_of_neighborSet_left_eq_empty
      w.property.2.symm hv.neighborSet_eq_empty w.property.1
  have := hempty
  change ¬ 2 ≤ Nat.card (componentDeleteVertex G v).ConnectedComponent
  rw [Nat.card_of_isEmpty]
  decide

theorem isolated_block_node : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.isolated_block_nodeType := by
  intro V _ G v hv
  let B : Block G := ⟨G.singletonSubgraph v, isolated_isBlock G v hv⟩
  refine ⟨B, rfl, ?_⟩
  intro x hx
  cases x with
  | inl C => exact hx
  | inr w =>
    have hw : w.val = v := hx
    exact isolated_not_cutVertex G v hv (hw ▸ w.property)

theorem componentBlockCutGraph_adjacency : Specs.FiniteCombinatorics.Graph.Blocks.Foundations.componentBlockCutGraph_adjacencyType := by intro V _ G c x y; rfl

end FiniteCombinatorics.Graph.Blocks
