import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.TreeExchange
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Specs.P205.Matroids.CycleCertificate
open _root_.FiniteCombinatorics.Matroid.Graphic
open Specs.P205.Matroids.Graphic Specs.P205.Matroids.TreeExchange
noncomputable section
universe u v

/-- Every label on the unique tree path has weight at most the entering edge.
For the finite nonempty path between distinct vertices this is precisely the
inequality against its maximum weight. Quantifying over paths avoids a choice
of the unique path; loops are explicitly excluded. -/
def CycleBound {α : Type u} {β : Type v} (G : Graph α β)
    (w : G.edgeSet → ℝ) (T : Set β) : Prop :=
  ∀ (e : G.edgeSet), e.val ∉ T → ∀ (x y : G.vertexSet),
    G.IsLink e.val x.val y.val → x ≠ y →
    ∀ (p : (spanningShadow G T).Walk x y), p.IsPath →
      ∀ (f : G.edgeSet), f.val ∈ pathLabels G T p → w f ≤ w e

/-- W48(2), with the maximum inequality expressed by all its finite members. -/
def MinimumIffCycleBound : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G),
    G.toSimpleGraph.Connected → ∀ (w : G.edgeSet → ℝ) (T : Set β),
      SpanningTreeValue G T →
      (MinimumSpanningTreeValue G hG w T ↔ CycleBound G w T)

/-- The displayed maximum-weight inequality in W48(2). The supremum is
an attained maximum, since a path between distinct vertices has a finite,
nonempty set of original labels; this fact is established in the proof. -/
def CycleMaximumBound {α : Type u} {β : Type v} (G : Graph α β)
    (w : G.edgeSet → ℝ) (T : Set β) : Prop :=
  ∀ (e : G.edgeSet), e.val ∉ T → ∀ (x y : G.vertexSet),
    G.IsLink e.val x.val y.val → x ≠ y →
    ∀ (p : (spanningShadow G T).Walk x y), p.IsPath →
      sSup (w '' {f : G.edgeSet | f.val ∈ pathLabels G T p}) ≤ w e

def MinimumIffCycleMaximum : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G),
    G.toSimpleGraph.Connected → ∀ (w : G.edgeSet → ℝ) (T : Set β),
      SpanningTreeValue G T →
      (MinimumSpanningTreeValue G hG w T ↔ CycleMaximumBound G w T)

end
end Specs.P205.Matroids.CycleCertificate
