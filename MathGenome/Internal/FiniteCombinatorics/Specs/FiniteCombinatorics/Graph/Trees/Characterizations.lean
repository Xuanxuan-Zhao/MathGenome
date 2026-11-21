import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Foundations

/-! Independent statements for paper.tex, W36. A spanning subgraph has the
same vertex type; its edges are a subset of the original edges. -/

universe u

namespace Specs.FiniteCombinatorics.Graph.Trees.Characterizations

open Specs.FiniteCombinatorics.Graph.Foundations

def tree_iff_edge_countType : Prop :=
  ∀ {V : Type u} [Finite V] [Nonempty V] (G : SimpleGraph V),
    TreeValue G ↔ G.Connected ∧ Nat.card G.edgeSet = Nat.card V - 1

/-- Equality is equality of vertex-simple paths with ordered endpoints.
This includes the length-zero path from a vertex to itself. -/
def tree_iff_unique_pathType : Prop :=
  ∀ {V : Type u} [Finite V] [Nonempty V] (G : SimpleGraph V),
    TreeValue G ↔ ∀ a b : V, ∃! _p : PathValue G a b, True

def spanning_treeType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    G.Connected → ∃ T : SimpleGraph V, T ≤ G ∧ TreeValue T

/-- No nonemptiness assumption: the same forest works on all components,
and its restriction to every original component is a spanning tree. -/
def spanning_forestType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    ∃ F : SimpleGraph V, F ≤ G ∧ ForestValue F ∧
      F.Reachable = G.Reachable ∧
      ∀ c : G.ConnectedComponent, TreeValue (F.induce c.supp)

end Specs.FiniteCombinatorics.Graph.Trees.Characterizations
