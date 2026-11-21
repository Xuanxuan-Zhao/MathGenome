import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Foundations

/-! Independent statements for paper.tex, W37. Degrees count neighbors,
and `edgeSet` consists of unordered pairs of distinct adjacent vertices.
The degree sum and parity statements allow an empty vertex type. -/

universe u

namespace Specs.FiniteCombinatorics.Graph.Trees.DegreesLeaves

open Specs.FiniteCombinatorics.Graph.Foundations

/-- Two distinct degree-one vertices, with precisely the source's size condition. -/
def two_leavesType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    TreeValue G → 2 ≤ Nat.card V →
      ∃ a b : V, a ≠ b ∧ degreeValue G a = 1 ∧ degreeValue G b = 1

/-- Handshaking, without nonemptiness or decidability assumptions on the graph. -/
def degree_sumType : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
    ∑ v : V, degreeValue G v = 2 * Nat.card G.edgeSet

/-- Natural subtraction includes the one-vertex tree. -/
def tree_degree_sumType : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
    TreeValue G → ∑ v : V, degreeValue G v = 2 * (Nat.card V - 1)

/-- Cardinality of the subtype of odd-degree vertices; valid also on no vertices. -/
def even_odd_degree_countType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    Even (Nat.card {v : V // Odd (degreeValue G v)})

end Specs.FiniteCombinatorics.Graph.Trees.DegreesLeaves
