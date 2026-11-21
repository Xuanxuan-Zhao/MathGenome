import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.GraphicBridge
import Mathlib.Analysis.Convex.Hull

/-! Graphic assertions of W46. Graphs have finite actual vertex and edge sets;
edge labels retain loops and parallel edges. Cardinality bounds use real subtraction.
All component counts retain isolated vertices, including the empty graph. -/
namespace Specs.P205.Matroids.Graphic
open _root_.P205.Matroids
noncomputable section
universe u v
attribute [local instance] Classical.propDecidable
set_option linter.checkUnivs false
set_option linter.unusedVariables false

def vertexInequalitiesType := ∀ {α : Type u} {β : Type v} (G : Graph α β)
  (hG : IsFiniteValue G), Set (G.edgeSet → ℝ)

def vertexInequalitiesValue : vertexInequalitiesType.{u,v} := fun G hG =>
  {x | (∀ e, 0 ≤ x e) ∧ ∀ S : Set _, S ⊆ G.vertexSet → S.Nonempty →
    subsetSumValue (graphicMatroidValue G hG) x (inducedEdgesValue G S) ≤ (S.ncard : ℝ) - 1}

def forestIndicatorsType := ∀ {α : Type u} {β : Type v} (G : Graph α β),
  Set (G.edgeSet → ℝ)

def forestIndicatorsValue : forestIndicatorsType.{u,v} := fun G =>
  {x | ∃ A, ForestValue G A ∧ ∀ e, x e = if e.val ∈ A then 1 else 0}

def spanningForestIndicatorsValue : forestIndicatorsType.{u,v} := fun G =>
  {x | ∃ A, SpanningForestValue G A ∧ ∀ e, x e = if e.val ∈ A then 1 else 0}

def spanningTreeIndicatorsValue : forestIndicatorsType.{u,v} := fun G =>
  {x | ∃ A, SpanningTreeValue G A ∧ ∀ e, x e = if e.val ∈ A then 1 else 0}

def VertexRankEquivalence : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G),
    vertexInequalitiesValue G hG = rankInequalitiesValue (graphicMatroidValue G hG)

def ForestPolytope : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G),
    convexHull ℝ (forestIndicatorsValue G) = vertexInequalitiesValue G hG

def SpanningForestPolytope : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G),
    convexHull ℝ (spanningForestIndicatorsValue G) =
      {x | x ∈ vertexInequalitiesValue G hG ∧
        subsetSumValue (graphicMatroidValue G hG) x G.edgeSet =
          (G.vertexSet.ncard : ℝ) - (componentCountValue G G.edgeSet : ℝ)}

def SpanningTreePolytope : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G),
    G.toSimpleGraph.Connected →
    convexHull ℝ (spanningTreeIndicatorsValue G) =
      {x | x ∈ vertexInequalitiesValue G hG ∧
        subsetSumValue (graphicMatroidValue G hG) x G.edgeSet =
          (G.vertexSet.ncard : ℝ) - 1}

/-- The singleton vertex inequality forces every labelled loop coordinate to zero. -/
def LoopZero : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G)
    (x : G.edgeSet → ℝ), x ∈ vertexInequalitiesValue G hG →
    ∀ e a (h : G.IsLink e a a), x ⟨e, h.edge_mem⟩ = 0

end
end Specs.P205.Matroids.Graphic
