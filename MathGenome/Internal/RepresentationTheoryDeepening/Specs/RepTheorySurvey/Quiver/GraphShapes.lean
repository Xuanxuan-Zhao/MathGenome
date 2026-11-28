import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.Forms
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace RepTheorySurvey.Quiver.GraphShapesSpec

universe u v

/-- The adjacency shadow retains which pairs have edges. Its multiplicities are
still given by `FormsSpec.edgeMultiplicity`. -/
def underlyingGraph {Q : Type u} [Quiver.{v} Q] : SimpleGraph Q where
  Adj i j := i ≠ j ∧ 0 < FormsSpec.edgeMultiplicity i j
  symm.symm i j h := ⟨h.1.symm, by simpa [FormsSpec.edgeMultiplicity, Nat.add_comm] using h.2⟩
  loopless.irrefl i h := h.1 rfl

/-- A spanning path, including the length-zero path on a single vertex. -/
def IsPathGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b : V, ∃ p : G.Walk a b, p.IsPath ∧ (∀ x, x ∈ p.support) ∧
    ∀ x y, G.Adj x y ↔ p.toSubgraph.Adj x y

/-- The three arms start with the three actual neighbors of the center, meet
only at that center, and exhaust both the vertices and the edges. -/
def IsThreeArmedTree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ c : V, (G.neighborSet c).ncard = 3 ∧
    ∃ (tip : G.neighborSet c → V) (arm : ∀ a, G.Walk c (tip a)),
      (∀ a, (arm a).IsPath ∧ 0 < (arm a).length ∧ (arm a).snd = a.val) ∧
      (∀ a b, a ≠ b → ∀ x, x ∈ (arm a).support → x ∈ (arm b).support → x = c) ∧
      (∀ x, x = c ∨ ∃ a, x ∈ (arm a).support) ∧
      (∀ x y, G.Adj x y ↔ ∃ a, (arm a).toSubgraph.Adj x y)

abbrev PositiveDefiniteMultiplicity : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] [Fintype (RM03.Arrow Q)],
    ¬ RM03.HasOrientedCycle Q → FormsSpec.PositiveDefinite Q →
    ∀ i j : Q, FormsSpec.edgeMultiplicity i j ≤ 1

abbrev PositiveDefiniteComponentTree : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] [Fintype (RM03.Arrow Q)],
    ¬ RM03.HasOrientedCycle Q → FormsSpec.PositiveDefinite Q →
    ∀ C : (underlyingGraph (Q := Q)).ConnectedComponent,
      let G := C.toSimpleGraph
      G.IsTree ∧ (∀ x, (G.neighborSet x).ncard ≤ 3) ∧
        ∀ x y, (G.neighborSet x).ncard = 3 → (G.neighborSet y).ncard = 3 → x = y

abbrev PositiveDefiniteComponentShapes : Prop :=
  ∀ {Q : Type u} [Quiver.{v} Q] [Fintype Q] [Fintype (RM03.Arrow Q)],
    ¬ RM03.HasOrientedCycle Q → FormsSpec.PositiveDefinite Q →
    ∀ C : (underlyingGraph (Q := Q)).ConnectedComponent,
      IsPathGraph C.toSimpleGraph ∨ IsThreeArmedTree C.toSimpleGraph

end RepTheorySurvey.Quiver.GraphShapesSpec
