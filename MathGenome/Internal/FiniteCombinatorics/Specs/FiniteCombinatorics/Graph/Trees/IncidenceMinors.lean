import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Trees.Incidence

/-! W42, incidence-minor classification. `S` is a subset of the actual unordered
edges of `G`. Its spanning graph keeps all vertices. A bijection `e` enumerates
the selected columns by the surviving row type, so the minor is square. Every
bijection is allowed; no order, connectedness of `G`, or field characteristic
is prescribed. The cardinality lemma ensures these bijections exist for every
selection of n-1 edges. -/

universe u v
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.Trees.IncidenceMinors
open _root_.FiniteCombinatorics.Graph.Trees

def selectedGraphType := ∀ {V : Type u} (G : SimpleGraph V), Finset G.edgeSet → SimpleGraph V

def selectedGraphValue : selectedGraphType := fun {_} G S =>
  SimpleGraph.fromEdgeSet (Subtype.val '' (S : Set G.edgeSet))

def incidenceMinorType := ∀ {V : Type u} (G : SimpleGraph V) (K : Type v) [Field K]
  (o : EdgeOrientation G) (r : V) (S : Finset G.edgeSet),
  ({x : V // x ≠ r} ≃ {a : G.edgeSet // a ∈ S}) →
  Matrix {x : V // x ≠ r} {x : V // x ≠ r} K

def incidenceMinorValue : incidenceMinorType := fun {_} G K _ o r _ e =>
  (Incidence.reducedIncidenceValue G K o r).submatrix id (fun i => (e i).val)

def minor_index_equivType : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (r : V) (S : Finset G.edgeSet),
  S.card = Fintype.card V - 1 →
  Nonempty ({x : V // x ≠ r} ≃ {a : G.edgeSet // a ∈ S})

def tree_minor_detType : Prop := by
  classical
  exact ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (K : Type v) [Field K]
    (o : EdgeOrientation G) (r : V) (S : Finset G.edgeSet)
    (e : {x : V // x ≠ r} ≃ {a : G.edgeSet // a ∈ S}),
    (selectedGraphValue G S).IsTree →
    (incidenceMinorValue G K o r S e).det = 1 ∨
      (incidenceMinorValue G K o r S e).det = -1

def non_tree_minor_detType : Prop := by
  classical
  exact ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (K : Type v) [Field K]
    (o : EdgeOrientation G) (r : V) (S : Finset G.edgeSet)
    (e : {x : V // x ≠ r} ≃ {a : G.edgeSet // a ∈ S}),
    S.card = Fintype.card V - 1 → ¬(selectedGraphValue G S).IsTree →
    (incidenceMinorValue G K o r S e).det = 0

def minor_det_sqType : Prop := by
  classical
  exact ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (K : Type v) [Field K]
    (o : EdgeOrientation G) (r : V) (S : Finset G.edgeSet)
    (e : {x : V // x ≠ r} ≃ {a : G.edgeSet // a ∈ S}),
    S.card = Fintype.card V - 1 →
    (incidenceMinorValue G K o r S e).det ^ 2 =
      if (selectedGraphValue G S).IsTree then 1 else 0

/-- The empty square minor for the single-vertex case has determinant one. -/
def singleton_minor_detType : Prop := by
  classical
  exact ∀ {V : Type u} [Fintype V] [Subsingleton V] (G : SimpleGraph V)
    (K : Type v) [Field K] (o : EdgeOrientation G) (r : V) (S : Finset G.edgeSet)
    (e : {x : V // x ≠ r} ≃ {a : G.edgeSet // a ∈ S}),
    (incidenceMinorValue G K o r S e).det = 1

end Specs.FiniteCombinatorics.Graph.Trees.IncidenceMinors
