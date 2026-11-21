import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Trees.ForestsBridges

/-! Independent definitions for paper.tex, chapter 6, the paragraph preceding W38.
The finite simple undirected conventions are those of W35. Cut vertices are tested
inside their original component, and 2-connectivity requires at least three vertices.
No block membership or block–cut tree assertion is assumed here. -/

universe u
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.Blocks.Foundations
open Specs.FiniteCombinatorics.Graph.Foundations
open Specs.FiniteCombinatorics.Graph.Trees.ForestsBridges

/-- Delete the vertex, with all incident edges; the remaining vertex type excludes it. -/
def deleteVertexType := ∀ {V : Type u} [Finite V], (G : SimpleGraph V) → (v : V) →
  SimpleGraph {w : V // w ≠ v}

def deleteVertexValue : deleteVertexType.{u} :=
  fun {_} _ G v => G.induce {w | w ≠ v}

/-- Delete v inside its original connected component, excluding all other components. -/
def componentDeleteVertexType := ∀ {V : Type u} [Finite V], (G : SimpleGraph V) → (v : V) →
  SimpleGraph {w : V // G.Reachable v w ∧ w ≠ v}

def componentDeleteVertexValue : componentDeleteVertexType.{u} :=
  fun {_} _ G v => G.induce {w | G.Reachable v w ∧ w ≠ v}

/-- A cut vertex of its own component, including for a disconnected ambient graph. -/
def CutVertexType := ∀ {V : Type u} [Finite V], SimpleGraph V → V → Prop

def CutVertexValue : CutVertexType.{u} :=
  fun {_} _ G v => 2 ≤ componentCountValue (componentDeleteVertexValue G v)

/-- The source convention excludes graphs on fewer than three vertices. -/
def TwoConnectedType := ∀ {V : Type u} [Finite V], SimpleGraph V → Prop

def TwoConnectedValue : TwoConnectedType.{u} :=
  fun {V} _ G => 3 ≤ Nat.card V ∧ G.Connected ∧
    ∀ v : V, (deleteVertexValue G v).Connected

/-- Maximal under inclusion of vertices and edges among all 2-connected subgraphs. -/
def MaximalTwoConnectedSubgraphType := ∀ {V : Type u} [Finite V], (G : SimpleGraph V) → G.Subgraph → Prop

def MaximalTwoConnectedSubgraphValue : MaximalTwoConnectedSubgraphType.{u} :=
  fun {_} _ G H => TwoConnectedValue H.coe ∧
    ∀ K : G.Subgraph, H ≤ K → TwoConnectedValue K.coe → K = H

/-- Exactly one bridge edge and its two endpoints; no additional isolated vertices. -/
def BridgeBlockType := ∀ {V : Type u} [Finite V], (G : SimpleGraph V) → G.Subgraph → Prop

def BridgeBlockValue : BridgeBlockType.{u} :=
  fun {V} _ G H => ∃ (a b : V) (hab : G.Adj a b),
    BridgeValue G s(a, b) ∧ H = G.subgraphOfAdj hab

/-- The singleton subgraph at an isolated vertex of the ambient graph. -/
def IsolatedBlockType := ∀ {V : Type u} [Finite V], (G : SimpleGraph V) → G.Subgraph → Prop

def IsolatedBlockValue : IsolatedBlockType.{u} :=
  fun {V} _ G H => ∃ v : V, G.IsIsolated v ∧ H = G.singletonSubgraph v

/-- The three kinds of block in the paragraph preceding W38. -/
def IsBlockType := ∀ {V : Type u} [Finite V], (G : SimpleGraph V) → G.Subgraph → Prop

def IsBlockValue : IsBlockType.{u} :=
  fun {_} _ G H => MaximalTwoConnectedSubgraphValue G H ∨
    BridgeBlockValue G H ∨ IsolatedBlockValue G H

/-- Blocks are actual subgraphs, identified by their vertices and edges. -/
def BlockType := ∀ {V : Type u} [Finite V], SimpleGraph V → Type u

def BlockValue : BlockType.{u} :=
  fun {_} _ G => {H : G.Subgraph // IsBlockValue G H}

/-- Separate block and cut-vertex nodes. All blocks, including isolated singletons, are retained. -/
def BlockCutNodeType := ∀ {V : Type u} [Finite V], SimpleGraph V → Type u

def BlockCutNodeValue : BlockCutNodeType.{u} :=
  fun {V} _ G => BlockValue G ⊕ {v : V // CutVertexValue G v}

/-- The bipartite incidence graph, with adjacency precisely vertex membership in a block. -/
def blockCutGraphType := ∀ {V : Type u} [Finite V], (G : SimpleGraph V) →
  SimpleGraph (BlockCutNodeValue G)

def blockCutGraphValue : blockCutGraphType.{u} :=
  fun {_} _ G => {
    Adj := fun x y => match x, y with
      | .inl B, .inr v => v.val ∈ B.val.verts
      | .inr v, .inl B => v.val ∈ B.val.verts
      | _, _ => False
    symm := ⟨by intro x y h; cases x <;> cases y <;> exact h⟩
    loopless := ⟨by intro x; cases x <;> exact not_false⟩ }

/-- The nodes associated with one original connected component. -/
def componentNodesType := ∀ {V : Type u} [Finite V], (G : SimpleGraph V) →
  G.ConnectedComponent → Set (BlockCutNodeValue G)

def componentNodesValue : componentNodesType.{u} :=
  fun {_} _ _G c x => match x with
    | .inl B => B.val.verts ⊆ c.supp
    | .inr v => v.val ∈ c.supp

/-- The componentwise block–cut incidence graph used in the statement of W38. -/
def componentBlockCutGraphType := ∀ {V : Type u} [Finite V], (G : SimpleGraph V) →
  (c : G.ConnectedComponent) → SimpleGraph (componentNodesValue G c)

def componentBlockCutGraphValue : componentBlockCutGraphType.{u} :=
  fun {_} _ G c => (blockCutGraphValue G).induce (componentNodesValue G c)

def deleteVertex_adjacencyType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (v : V)
    (a b : {w : V // w ≠ v}),
    (deleteVertexValue G v).Adj a b ↔ G.Adj a.val b.val

def componentDeleteVertex_adjacencyType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (v : V)
    (a b : {w : V // G.Reachable v w ∧ w ≠ v}),
    (componentDeleteVertexValue G v).Adj a b ↔ G.Adj a.val b.val

def cutVertex_iffType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (v : V),
    CutVertexValue G v ↔
      2 ≤ Nat.card (G.induce {w | G.Reachable v w ∧ w ≠ v}).ConnectedComponent

def twoConnected_iffType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    TwoConnectedValue G ↔ 3 ≤ Nat.card V ∧ G.Connected ∧
      ∀ v : V, (G.induce {w | w ≠ v}).Connected

def isBlock_iffType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (H : G.Subgraph),
    IsBlockValue G H ↔
      (TwoConnectedValue H.coe ∧
        ∀ K : G.Subgraph, H ≤ K → TwoConnectedValue K.coe → K = H) ∨
      (∃ (a b : V) (hab : G.Adj a b), BridgeValue G s(a, b) ∧ H = G.subgraphOfAdj hab) ∨
      (∃ v : V, G.IsIsolated v ∧ H = G.singletonSubgraph v)

def blockCutGraph_adjacencyType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V)
    (B : BlockValue G) (v : {v : V // CutVertexValue G v}),
    (blockCutGraphValue G).Adj (.inl B) (.inr v) ↔ v.val ∈ B.val.verts

def blockCutGraph_bipartiteType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    (∀ B C : BlockValue G, ¬ (blockCutGraphValue G).Adj (.inl B) (.inl C)) ∧
    (∀ v w : {v : V // CutVertexValue G v},
      ¬ (blockCutGraphValue G).Adj (.inr v) (.inr w))

def isolated_isBlockType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (v : V),
    G.IsIsolated v → IsBlockValue G (G.singletonSubgraph v)

def isolated_not_cutVertexType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (v : V),
    G.IsIsolated v → ¬ CutVertexValue G v

def isolated_block_nodeType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (v : V),
    G.IsIsolated v → ∃ B : BlockValue G,
      B.val = G.singletonSubgraph v ∧
      ∀ x : BlockCutNodeValue G, ¬ (blockCutGraphValue G).Adj (.inl B) x

def componentBlockCutGraph_adjacencyType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (c : G.ConnectedComponent)
    (x y : componentNodesValue G c),
    (componentBlockCutGraphValue G c).Adj x y ↔ (blockCutGraphValue G).Adj x.val y.val

end Specs.FiniteCombinatorics.Graph.Blocks.Foundations
