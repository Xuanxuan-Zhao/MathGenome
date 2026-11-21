import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.GreedyBasis
import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.GraphicBridge

/-! Independent specification of paper.tex, Theorem 9.5 (W47).
The scan uses actual edge labels and the cycle-free multigraph forest predicate.
Only the actual vertex and edge sets are finite. Real weights have no sign
restriction, and no order is prescribed within a block of equal weights. -/
namespace Specs.P205.Matroids.Graphic
noncomputable section
set_option linter.checkUnivs false
universe u v

/-- Accept precisely those insertions which leave a forest. -/
def kruskalStepType := ∀ {α : Type u} {β : Type v} (G : Graph α β),
  Set β → G.edgeSet → Set β

def kruskalStepValue : kruskalStepType.{u, v} := fun {_} {_} G I e => by
  classical
  exact if ForestValue G (insert e.val I) then insert e.val I else I

/-- State after scanning a prefix, starting with the empty forest. -/
def kruskalStateType := ∀ {α : Type u} {β : Type v} (G : Graph α β),
  List G.edgeSet → ℕ → Set β

def kruskalStateValue : kruskalStateType.{u, v} := fun {_} {_} G l i =>
  (l.take i).foldl (kruskalStepValue G) ∅

/-- Output after all edges, including edges of negative weight, have been scanned. -/
def kruskalOutputType := ∀ {α : Type u} {β : Type v} (G : Graph α β),
  List G.edgeSet → Set β

def kruskalOutputValue : kruskalOutputType.{u, v} := fun {_} {_} G l =>
  kruskalStateValue G l l.length

/-- An exhaustive nondecreasing order, allowing arbitrary ties. -/
def KruskalOrderingType := ∀ {α : Type u} {β : Type v} (G : Graph α β),
  (G.edgeSet → ℝ) → List G.edgeSet → Prop

def KruskalOrderingValue : KruskalOrderingType.{u, v} := fun {_} {_} _ w l =>
  l.Nodup ∧ (∀ e, e ∈ l) ∧ l.Pairwise (fun a b => w a ≤ w b)

/-- The actual forest scan agrees at every prefix with graphic-matroid greedy. -/
def KruskalStateEqGreedy : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G)
    (l : List G.edgeSet) (i : ℕ),
    kruskalStateValue G l i = greedyStateValue (graphicMatroidValue G hG) l i

/-- Minimum weight is compared with spanning forests of the original graph. -/
def KruskalMinimumForest : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G)
    (w : G.edgeSet → ℝ) (l : List G.edgeSet), KruskalOrderingValue G w l →
    MinimumSpanningForestValue G hG w (kruskalOutputValue G l)

/-- Connectedness includes a nonempty actual vertex set. -/
def KruskalMinimumTree : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G),
    G.toSimpleGraph.Connected → ∀ (w : G.edgeSet → ℝ) (l : List G.edgeSet),
    KruskalOrderingValue G w l →
    MinimumSpanningTreeValue G hG w (kruskalOutputValue G l)

/-- An edge-free graph, including one with isolated vertices, has empty output. -/
def KruskalEmptyEdges : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β), G.edgeSet = ∅ →
    ∀ l : List G.edgeSet, kruskalOutputValue G l = ∅

/-- In particular the graph with no vertices has empty output. -/
def KruskalEmptyVertices : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β), G.vertexSet = ∅ →
    ∀ l : List G.edgeSet, kruskalOutputValue G l = ∅

end
end Specs.P205.Matroids.Graphic
