import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Blocks.Foundations

/-! Independent statement of paper.tex, p204:brooks-order.
The graph is finite, simple and undirected. Two-connectivity includes the
at-least-three-vertices condition; degree is the cardinality of the neighbor set.
Deleting the two vertices retains exactly the other vertices and their edges. -/

universe u
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.Coloring.BrooksOrder
open Specs.FiniteCombinatorics.Graph.Blocks.Foundations
open Specs.FiniteCombinatorics.Graph.Foundations

def two_initial_verticesType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    TwoConnectedValue G → G ≠ ⊤ → (∀ x : V, 3 ≤ degreeValue G x) →
    ∃ v a b : V, a ≠ b ∧ G.Adj v a ∧ G.Adj v b ∧ ¬ G.Adj a b ∧
      (G.induce {x | x ≠ a ∧ x ≠ b}).Connected

end Specs.FiniteCombinatorics.Graph.Coloring.BrooksOrder
