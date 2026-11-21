import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.TreeExchange

/-! The safe-cut assertion of paper.tex W48(1). Cuts use the actual vertex
subtype, so ambient vertices outside the graph play no role. -/
namespace Specs.P205.Matroids.SafeCutEdge
open Specs.P205.Matroids.Graphic
noncomputable section
universe u v

/-- A labelled edge crosses a vertex cut if its endpoints lie on opposite sides.
The order of its endpoints is immaterial since `Graph.IsLink` is symmetric. -/
def Crosses {α : Type u} {β : Type v} (G : Graph α β)
    (S : Set G.vertexSet) (e : β) : Prop :=
  ∃ x y : G.vertexSet, x ∈ S ∧ y ∉ S ∧ G.IsLink e x.val y.val

def CutNonempty : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β), G.toSimpleGraph.Connected →
    ∀ S : Set G.vertexSet, S.Nonempty → S ≠ Set.univ →
      ∃ e : G.edgeSet, Crosses G S e.val

/-- Every light edge of a cut respecting an optimally extendible forest is safe.
Weights range over all reals, with no distinctness or positivity restriction. -/
def SafeEdge : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G),
    G.toSimpleGraph.Connected → ∀ (w : G.edgeSet → ℝ) (F : Set β),
    ForestValue G F →
    (∃ D, MinimumSpanningTreeValue G hG w D ∧ F ⊆ D) →
    ∀ S : Set G.vertexSet, S.Nonempty → S ≠ Set.univ →
    (∀ f ∈ F, ¬ Crosses G S f) →
    ∀ e : G.edgeSet, Crosses G S e.val →
    (∀ f : G.edgeSet, Crosses G S f.val → w e ≤ w f) →
      ∃ D, MinimumSpanningTreeValue G hG w D ∧ insert e.val F ⊆ D

end
end Specs.P205.Matroids.SafeCutEdge
