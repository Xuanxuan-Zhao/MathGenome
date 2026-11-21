import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.GraphicBridge

/-! Structural exchanges used in paper.tex W48, for original edge labels.
A path in the simple shadow determines its labels uniquely because the selected
labelled tree is simple. No simplicity hypothesis is imposed on the ambient graph. -/
namespace Specs.P205.Matroids.TreeExchange
open _root_.FiniteCombinatorics.Matroid.Graphic
open Specs.P205.Matroids.Graphic
noncomputable section
set_option linter.unusedVariables false
universe u v

/-- Original labels traversed by a shadow walk, with membership in T retained. -/
def pathLabels {α : Type u} {β : Type v} (G : Graph α β) (T : Set β)
    {x y : G.vertexSet} (p : (spanningShadow G T).Walk x y) : Set β :=
  {f | f ∈ T ∧ ∃ a b : G.vertexSet, G.IsLink f a.val b.val ∧ s(a,b) ∈ p.edges}

def UniquePath : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (T : Set β),
    SpanningTreeValue G T → ∀ x y : G.vertexSet,
      ∃! p : (spanningShadow G T).Walk x y, p.IsPath

def PathLabelsNonempty : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (T : Set β),
    ∀ {x y : G.vertexSet} (p : (spanningShadow G T).Walk x y),
      x ≠ y → (pathLabels G T p).Nonempty

def PathExchange : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G)
    (hC : G.toSimpleGraph.Connected) (T : Set β), SpanningTreeValue G T →
    ∀ {e : β} {x y : G.vertexSet}, G.IsLink e x.val y.val → e ∉ T → x ≠ y →
    ∀ (p : (spanningShadow G T).Walk x y), p.IsPath → ∀ f ∈ T,
      SpanningTreeValue G (insert e (T \ {f})) ↔ f ∈ pathLabels G T p

/-- Exactly two connected components, with the removed edge's endpoints separated. -/
def DeleteTreeEdge : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G)
    (T : Set β), SpanningTreeValue G T → ∀ {f : β}, f ∈ T →
    ∀ {a b : G.vertexSet}, G.IsLink f a.val b.val →
      spanningComponentCount G (T \ {f}) = 2 ∧
      ¬ (spanningShadow G (T \ {f})).Reachable a b ∧
      ∀ z : G.vertexSet, (spanningShadow G (T \ {f})).Reachable a z ∨
        (spanningShadow G (T \ {f})).Reachable b z

/-- A replacement reconnects the two components precisely when its ends are in
opposite components. The condition also allows reinserting the removed edge. -/
def CutExchange : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G)
    (hC : G.toSimpleGraph.Connected) (T : Set β), SpanningTreeValue G T →
    ∀ {f : β}, f ∈ T → ∀ {e : β} {x y : G.vertexSet},
    G.IsLink e x.val y.val → e ∉ T \ {f} →
      (SpanningTreeValue G (insert e (T \ {f})) ↔
        ¬ (spanningShadow G (T \ {f})).Reachable x y)

/-- Any edge crossing the deletion cut reconnects it, without a separate
nonmembership assumption on the new label. -/
def CrossingReconnects : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G)
    (hC : G.toSimpleGraph.Connected) (T : Set β), SpanningTreeValue G T →
    ∀ {f : β}, f ∈ T → ∀ {e : β} {x y : G.vertexSet},
    G.IsLink e x.val y.val →
    ¬ (spanningShadow G (T \ {f})).Reachable x y →
      SpanningTreeValue G (insert e (T \ {f}))

end
end Specs.P205.Matroids.TreeExchange
