import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.MultigraphFoundation
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Trees.Incidence
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.VectorRepresentation
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Combinatorics.Graph.Delete

/-! Indexed walks, cycles and signed columns for paper.tex W72.
The vertex and edge label types can be infinite. Only the actual sets are finite.
Cycles use cyclic indexing, so length one is a loop and length two uses two
separate edge labels. No characteristic restriction occurs in any statement. -/
universe u v w z
noncomputable section
namespace FiniteCombinatorics.Matroid.Graphic

/-- A walk records the identity of every traversed edge, including loops. -/
structure Walk {α : Type u} {β : Type v} (G : _root_.Graph α β) (n : ℕ) where
  vertex : Fin (n + 1) → G.vertexSet
  edge : Fin n → β
  link : ∀ i, G.IsLink (edge i) (vertex i.castSucc) (vertex i.succ)

/-- A vertex-simple closed indexed traversal. The last-to-first edge is
included by the cyclic successor permutation. -/
structure Cycle {α : Type u} {β : Type v} (G : _root_.Graph α β) (n : ℕ) where
  positive : 0 < n
  vertex : Fin n → α
  edge : Fin n → β
  vertex_injective : Function.Injective vertex
  edge_injective : Function.Injective edge
  link : ∀ i, G.IsLink (edge i) (vertex i) (vertex (finRotate n i))

/-- Forests are subsets of the actual edge set with no indexed cycle. -/
def Forest {α : Type u} {β : Type v} (G : _root_.Graph α β) (A : Set β) : Prop :=
  A ⊆ G.edgeSet ∧ ∀ n (c : Cycle G n), ¬ Set.range c.edge ⊆ A

/-- Both ends of every actual edge, with a freely chosen order. Loops have equal ends. -/
structure Orientation {α : Type u} {β : Type v} (G : _root_.Graph α β) where
  tail : G.edgeSet → α
  head : G.edgeSet → α
  link : ∀ e, G.IsLink e.val (tail e) (head e)

/-- Columns live in the actual vertex coordinate space. Values outside the
graph's edge set are zero and play no role in its vector matroid. -/
def column {α : Type u} {β : Type v} (G : _root_.Graph α β)
    (K : Type w) [Field K] (o : Orientation G) (e : β) : G.vertexSet → K := by
  classical
  exact if he : e ∈ G.edgeSet then
    fun x => (if x.val = o.head ⟨e, he⟩ then 1 else 0) -
      (if x.val = o.tail ⟨e, he⟩ then 1 else 0)
  else 0

/-- The canonical finite vector matroid on the original edge labels. -/
def incidenceMatroid {α : Type u} {β : Type v} (G : _root_.Graph α β)
    (hG : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G)
    (K : Type w) [Field K] (o : Orientation G) : _root_.Matroid β :=
  Expected.vectorMatroid K G.edgeSet hG.2 (column G K o)

end FiniteCombinatorics.Matroid.Graphic

namespace Specs.FiniteCombinatorics.Matroid.GraphicIncidence
open _root_.FiniteCombinatorics.Matroid.Graphic

def orientation_exists : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β), Nonempty (Orientation G)

def column_loop : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β)
    (K : Type w) [Field K] (o : Orientation G) {e : β} {x : α},
    G.IsLink e x x → column G K o e = 0

/-- No assumption of a finite ambient label type or characteristic zero. -/
def columns_independent_iff_forest : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β)
    (hG : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G)
    (K : Type w) [Field K] (o : Orientation G) (A : Set β),
    A ⊆ G.edgeSet → (LinearIndepOn K (column G K o) A ↔ Forest G A)

def incidenceMatroid_indep : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β)
    (hG : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G)
    (K : Type w) [Field K] (o : Orientation G) (A : Set β),
    (incidenceMatroid G hG K o).Indep A ↔ Forest G A

def incidenceMatroid_invariant : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β)
    (hG : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G)
    (K : Type w) [Field K] (L : Type z) [Field L]
    (o p : Orientation G), incidenceMatroid G hG K o = incidenceMatroid G hG L p

/-- The incidence function agrees with the accepted simple-graph matrix,
including its row/column indexing conventions. -/
def simple_columns : Prop :=
  ∀ {α : Type u} (G : SimpleGraph α) (K : Type w) [Field K]
    (o : _root_.FiniteCombinatorics.Graph.Trees.EdgeOrientation G),
    ∃ p : Orientation (_root_.Graph.ofSimpleGraph G),
      ∀ (e : G.edgeSet) (x : (_root_.Graph.ofSimpleGraph G).vertexSet),
        column (_root_.Graph.ofSimpleGraph G) K p e.val x =
          Specs.FiniteCombinatorics.Graph.Trees.Incidence.incidenceValue G K o x.val e

/-- On simple graphs the forest notion is the accepted Mathlib acyclicity. -/
def simple_forest : Prop :=
  ∀ {α : Type u} (G : SimpleGraph α),
    Forest (_root_.Graph.ofSimpleGraph G) G.edgeSet ↔ G.IsAcyclic

/-- Specialization on every edge subset, using the original unordered edge labels. -/
def simple_subset_forest : Prop :=
  ∀ {α : Type u} (G : SimpleGraph α) (A : Set (Sym2 α)), A ⊆ G.edgeSet →
    (Forest (_root_.Graph.ofSimpleGraph G) A ↔ (SimpleGraph.fromEdgeSet A).IsAcyclic)

end Specs.FiniteCombinatorics.Matroid.GraphicIncidence
