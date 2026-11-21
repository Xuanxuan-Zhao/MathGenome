import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.CycleCertificate

/-! W48(3): the strict cycle certificate, with actual multigraph edge labels.
No distinctness assumption is imposed on the weights. -/
namespace Specs.P205.Matroids.UniqueCycleCertificate
open _root_.FiniteCombinatorics.Matroid.Graphic
open Specs.P205.Matroids.Graphic Specs.P205.Matroids.TreeExchange
noncomputable section
universe u v

/-- The strict certificate expressed for every label on the unique tree path.
Loops are excluded by the distinct-endpoint condition. -/
def StrictCycleBound {α : Type u} {β : Type v} (G : Graph α β)
    (w : G.edgeSet → ℝ) (T : Set β) : Prop :=
  ∀ (e : G.edgeSet), e.val ∉ T → ∀ (x y : G.vertexSet),
    G.IsLink e.val x.val y.val → x ≠ y →
    ∀ (p : (spanningShadow G T).Walk x y), p.IsPath →
      ∀ (f : G.edgeSet), f.val ∈ pathLabels G T p → w f < w e

/-- The displayed strict maximum inequality of W48(3). -/
def StrictCycleMaximumBound {α : Type u} {β : Type v} (G : Graph α β)
    (w : G.edgeSet → ℝ) (T : Set β) : Prop :=
  ∀ (e : G.edgeSet), e.val ∉ T → ∀ (x y : G.vertexSet),
    G.IsLink e.val x.val y.val → x ≠ y →
    ∀ (p : (spanningShadow G T).Walk x y), p.IsPath →
      sSup (w '' {f : G.edgeSet | f.val ∈ pathLabels G T p}) < w e

def UniqueMinimumIffStrictCycleBound : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G),
    G.toSimpleGraph.Connected → ∀ (w : G.edgeSet → ℝ) (T : Set β),
      SpanningTreeValue G T →
      (UniqueMinimumSpanningTreeValue G hG w T ↔ StrictCycleBound G w T)

def UniqueMinimumIffStrictCycleMaximum : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G),
    G.toSimpleGraph.Connected → ∀ (w : G.edgeSet → ℝ) (T : Set β),
      SpanningTreeValue G T →
      (UniqueMinimumSpanningTreeValue G hG w T ↔ StrictCycleMaximumBound G w T)

/-- Equality with the path maximum in a minimum tree produces a different
minimum tree with exactly the same weight. -/
def EqualityMaximumAlternative : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G),
    G.toSimpleGraph.Connected → ∀ (w : G.edgeSet → ℝ) (T : Set β),
      MinimumSpanningTreeValue G hG w T →
      ∀ (e : G.edgeSet), e.val ∉ T → ∀ (x y : G.vertexSet),
        G.IsLink e.val x.val y.val → x ≠ y →
        ∀ (p : (spanningShadow G T).Walk x y), p.IsPath →
          w e = sSup (w '' {f : G.edgeSet | f.val ∈ pathLabels G T p}) →
          ∃ D, D ≠ T ∧ MinimumSpanningTreeValue G hG w D ∧
            edgeWeightValue G hG w D = edgeWeightValue G hG w T

end
end Specs.P205.Matroids.UniqueCycleCertificate
