import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Trees.IncidenceMinors
import Mathlib.Data.Finset.Powerset

/-! W42. Spanning trees are subsets of the actual unordered edges, retaining
all vertices. The sum includes every such tree, with no choice of orientation
or enumeration in its statement. -/
universe u v
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.Trees.MatrixTree

def spanningTreesType := ∀ {V : Type u} (G : SimpleGraph V) [Fintype G.edgeSet],
  Finset (Finset G.edgeSet)

def spanningTreesValue : spanningTreesType := fun {_} G _ => by
  classical
  exact Finset.univ.powerset.filter (fun S => (IncidenceMinors.selectedGraphValue G S).IsTree)

def mem_spanningTreesType : Prop :=
  ∀ {V : Type u} (G : SimpleGraph V) [Fintype G.edgeSet] (S : Finset G.edgeSet),
    S ∈ spanningTreesValue G ↔ (IncidenceMinors.selectedGraphValue G S).IsTree

/-- Each spanning tree graph is represented once, so the finite subset sum
and its cardinality count the usual spanning trees. -/
def spanning_tree_selectionsType : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (T : SimpleGraph V), T ≤ G → T.IsTree →
    ∃! S : Finset G.edgeSet, S ∈ spanningTreesValue G ∧
      IncidenceMinors.selectedGraphValue G S = T

def weighted_matrix_treeType : Prop := by
  classical
  exact ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (K : Type v) [Field K] (w : G.edgeSet → K) (r : V),
    (Incidence.principalMinorValue (Incidence.weightedLaplacianValue G K w) r).det =
      ∑ S ∈ spanningTreesValue G, ∏ e ∈ S, w e

def matrix_tree_countType : Prop := by
  classical
  exact ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet] (r : V),
    (Incidence.principalMinorValue
      (Incidence.weightedLaplacianValue G ℚ (fun _ => 1)) r).det =
      ((spanningTreesValue G).card : ℚ)

def disconnected_minorType : Prop := by
  classical
  exact ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (K : Type v) [Field K] (w : G.edgeSet → K) (r : V), ¬G.Connected →
    (Incidence.principalMinorValue (Incidence.weightedLaplacianValue G K w) r).det = 0

def singleton_minorType : Prop := by
  classical
  exact ∀ {V : Type u} [Fintype V] [Subsingleton V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (K : Type v) [Field K] (w : G.edgeSet → K) (r : V),
    (Incidence.principalMinorValue (Incidence.weightedLaplacianValue G K w) r).det = 1

end Specs.FiniteCombinatorics.Graph.Trees.MatrixTree
