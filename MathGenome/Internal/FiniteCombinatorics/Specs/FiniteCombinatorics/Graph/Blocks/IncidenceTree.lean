import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Blocks.Foundations

/-! W38: the incidence graph uses precisely the blocks and component-local
cut vertices of the shared foundations, including isolated singleton blocks. -/
universe u
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.Blocks.IncidenceTree
open Specs.FiniteCombinatorics.Graph.Blocks.Foundations

/-- The actual block–cut incidence graph of every connected component is a tree. -/
def componentBlockCutGraph_isTreeType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (c : G.ConnectedComponent),
    (componentBlockCutGraphValue G c).IsTree

/-- An isolated component has exactly its singleton block node and no cut node. -/
def isolated_component_nodesType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (v : V),
    G.IsIsolated v → ∃ B : BlockValue G,
      B.val = G.singletonSubgraph v ∧
      componentNodesValue G (G.connectedComponentMk v) = {Sum.inl B}

end Specs.FiniteCombinatorics.Graph.Blocks.IncidenceTree
