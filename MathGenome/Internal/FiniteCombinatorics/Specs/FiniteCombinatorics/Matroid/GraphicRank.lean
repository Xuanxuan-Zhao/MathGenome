import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.GraphicIncidence
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.ForwardPresentations

/-! W72 and the subset-rank formula used in W77. All restrictions are spanning:
isolated vertices remain present. Ambient label types need not be finite. -/
universe u v w
noncomputable section
namespace FiniteCombinatorics.Matroid.Graphic

instance incidenceMatroidFinite {α : Type u} {β : Type v} (G : _root_.Graph α β)
    (hG : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G)
    (K : Type w) [Field K] (o : Orientation G) :
    (incidenceMatroid G hG K o).Finite := by
  unfold incidenceMatroid
  infer_instance

/-- Adjacency of the spanning edge restriction, discarding only loops and multiplicity. -/
def spanningShadow {α : Type u} {β : Type v} (G : _root_.Graph α β)
    (A : Set β) : SimpleGraph G.vertexSet := (G.restrict A).toSimpleGraph

/-- Components include isolated vertices, and there are none if there are no vertices. -/
def spanningComponentCount {α : Type u} {β : Type v} (G : _root_.Graph α β)
    (A : Set β) : ℕ := Nat.card (spanningShadow G A).ConnectedComponent

/-- A forest spanning each component of the specified edge subgraph. The forest
condition retains edge identities, excluding loops and pairs of parallel edges. -/
def SpanningForest {α : Type u} {β : Type v} (G : _root_.Graph α β)
    (B A : Set β) : Prop :=
  B ⊆ A ∧ Forest G B ∧ ∀ x y : G.vertexSet,
    (spanningShadow G A).Reachable x y → (spanningShadow G B).Reachable x y

end FiniteCombinatorics.Matroid.Graphic
namespace Specs.FiniteCombinatorics.Matroid.GraphicRank
open _root_.FiniteCombinatorics.Matroid.Graphic

/-- Forgetting loops and parallel multiplicity preserves the walk relation. -/
def shadow_reachable_iff : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) (A : Set β)
    (x y : G.vertexSet),
    (spanningShadow G A).Reachable x y ↔ Relation.ReflTransGen
      (fun a b : G.vertexSet => ∃ e ∈ A, G.IsLink e a.val b.val) x y

def basis_iff_spanningForest : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β)
    (hG : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G)
    (K : Type w) [Field K] (o : Orientation G) (B A : Set β), A ⊆ G.edgeSet →
    ((incidenceMatroid G hG K o).IsBasis B A ↔ SpanningForest G B A)

/-- Explicit component-tree formulation. Simplicity of the selected graph
records that a tree cannot use a loop or two parallel edge identities. -/
def basis_iff_component_trees : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β)
    (hG : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G)
    (K : Type w) [Field K] (o : Orientation G) (B A : Set β), A ⊆ G.edgeSet →
    ((incidenceMatroid G hG K o).IsBasis B A ↔ B ⊆ A ∧ (G.restrict B).Simple ∧
      ∀ C : (spanningShadow G A).ConnectedComponent,
        ((spanningShadow G B).induce C.supp).IsTree)

def base_iff_spanningForest : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β)
    (hG : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G)
    (K : Type w) [Field K] (o : Orientation G) (B : Set β),
    ((incidenceMatroid G hG K o).IsBase B ↔ SpanningForest G B G.edgeSet)

def base_iff_component_trees : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β)
    (hG : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G)
    (K : Type w) [Field K] (o : Orientation G) (B : Set β),
    ((incidenceMatroid G hG K o).IsBase B ↔ B ⊆ G.edgeSet ∧ (G.restrict B).Simple ∧
      ∀ C : (spanningShadow G G.edgeSet).ConnectedComponent,
        ((spanningShadow G B).induce C.supp).IsTree)

def component_tree : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) (B A : Set β),
    SpanningForest G B A → ∀ C : (spanningShadow G A).ConnectedComponent,
      ((spanningShadow G B).induce C.supp).IsTree

def forest_extension : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β)
    (_hG : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G)
    (I A : Set β), Forest G I → I ⊆ A → A ⊆ G.edgeSet →
    ∃ B, I ⊆ B ∧ SpanningForest G B A

def rank_eq_vertices_sub_components : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β)
    (hG : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G)
    (K : Type w) [Field K] (o : Orientation G) (A : Set β), A ⊆ G.edgeSet →
    _root_.FiniteCombinatorics.Matroid.Expected.rank (incidenceMatroid G hG K o) A =
      (G.vertexSet.ncard : ℤ) - (spanningComponentCount G A : ℤ)

def total_rank : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β)
    (hG : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G)
    (K : Type w) [Field K] (o : Orientation G),
    _root_.FiniteCombinatorics.Matroid.Expected.rank (incidenceMatroid G hG K o) G.edgeSet =
      (G.vertexSet.ncard : ℤ) - (Nat.card G.toSimpleGraph.ConnectedComponent : ℤ)

def forest_cardinality : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β)
    (_hG : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G)
    (A : Set β), Forest G A →
    A.ncard + spanningComponentCount G A = G.vertexSet.ncard

end Specs.FiniteCombinatorics.Matroid.GraphicRank
