import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.SafeCutEdge

/-! Prim's algorithm in W48(1), paper.tex 2220–2221 and 2242–2248.
The visited vertices are actual vertices; edge labels retain multiplicity.
A legal transition makes only a minimum-cut choice. In particular neither
foresthood nor optimal extendibility is built into legality. -/
namespace Specs.P205.Matroids.Prim
open _root_.FiniteCombinatorics.Matroid.Graphic
open Specs.P205.Matroids.Graphic
open Specs.P205.Matroids.SafeCutEdge
noncomputable section
set_option linter.unusedVariables false
universe u v
variable {α : Type u} {β : Type v}

/-- Choose any light crossing label, orient it outwards, and add its new end. -/
def Step (G : Graph α β) (w : G.edgeSet → ℝ)
    (S : Set G.vertexSet) (F : Set β) (S' : Set G.vertexSet) (F' : Set β) : Prop :=
  ∃ (e : G.edgeSet) (x y : G.vertexSet),
    x ∈ S ∧ y ∉ S ∧ G.IsLink e.val x.val y.val ∧
    (∀ f : G.edgeSet, Crosses G S f.val → w e ≤ w f) ∧
    S' = insert y S ∧ F' = insert e.val F

/-- All finite legal histories, indexed by the number of additions. -/
inductive Run (G : Graph α β) (w : G.edgeSet → ℝ) (r : G.vertexSet) :
    ℕ → Set G.vertexSet → Set β → Prop
  | start : Run G w r 0 {r} ∅
  | next {n S F S' F'} : Run G w r n S F → Step G w S F S' F' →
      Run G w r (n + 1) S' F'

/-- Foresthood, internal endpoints, and root connectivity say the chosen labels
form a tree on precisely the visited vertices (with unvisited vertices isolated).
The counts also record that each transition adds one vertex and one label. -/
def PartialTree (G : Graph α β) (r : G.vertexSet) (n : ℕ)
    (S : Set G.vertexSet) (F : Set β) : Prop :=
  S.ncard = n + 1 ∧ F.ncard = n ∧ r ∈ S ∧ ForestValue G F ∧
  (∀ f ∈ F, ∀ x y : G.vertexSet, G.IsLink f x.val y.val → x ∈ S ∧ y ∈ S) ∧
  (∀ x ∈ S, (spanningShadow G F).Reachable r x)

def RunInvariants : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G),
    G.toSimpleGraph.Connected → ∀ (w : G.edgeSet → ℝ) (r : G.vertexSet)
    (n : ℕ) (S : Set G.vertexSet) (F : Set β), Run G w r n S F →
    PartialTree G r n S F ∧
      ∃ D, MinimumSpanningTreeValue G hG w D ∧ F ⊆ D

def StepAvailable : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (_hG : IsFiniteValue G),
    G.toSimpleGraph.Connected → ∀ (w : G.edgeSet → ℝ) (r : G.vertexSet)
    (n : ℕ) (S : Set G.vertexSet) (F : Set β), Run G w r n S F → S ≠ Set.univ →
    ∃ S' F', Step G w S F S' F' ∧ Run G w r (n + 1) S' F'

def RunLength : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (_hG : IsFiniteValue G),
    G.toSimpleGraph.Connected → ∀ (w : G.edgeSet → ℝ) (r : G.vertexSet)
    (n : ℕ) (S : Set G.vertexSet) (F : Set β), Run G w r n S F →
    n ≤ G.vertexSet.ncard - 1 ∧ (S = Set.univ ↔ n = G.vertexSet.ncard - 1)

/-- A legal history is maximal exactly at the stated stopping count. -/
def RunTermination : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G),
    G.toSimpleGraph.Connected → ∀ (w : G.edgeSet → ℝ) (r : G.vertexSet)
    (n : ℕ) (S : Set G.vertexSet) (F : Set β), Run G w r n S F →
    ((¬ ∃ S' F', Step G w S F S' F') ↔ n = G.vertexSet.ncard - 1)

def RunMinimum : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G),
    G.toSimpleGraph.Connected → ∀ (w : G.edgeSet → ℝ) (r : G.vertexSet)
    (n : ℕ) (S : Set G.vertexSet) (F : Set β), Run G w r n S F → S = Set.univ →
    MinimumSpanningTreeValue G hG w F ∧ n = G.vertexSet.ncard - 1

/-- Every legal prefix can be completed, preserving all its chosen labels.
Together with `RunLength` and `StepAvailable`, this gives termination after
exactly |V|-1 additions for every choice of light edges, including ties. -/
def RunCompletion : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G),
    G.toSimpleGraph.Connected → ∀ (w : G.edgeSet → ℝ) (r : G.vertexSet)
    (n : ℕ) (S : Set G.vertexSet) (F : Set β), Run G w r n S F →
    ∃ F', Run G w r (G.vertexSet.ncard - 1) Set.univ F' ∧ F ⊆ F' ∧
      MinimumSpanningTreeValue G hG w F'

/-- A completed run exists from every start, even on a singleton graph. -/
def PrimCorrect : Prop :=
  ∀ {α : Type u} {β : Type v} (G : Graph α β) (hG : IsFiniteValue G),
    G.toSimpleGraph.Connected → ∀ (w : G.edgeSet → ℝ) (r : G.vertexSet),
    ∃ F, Run G w r (G.vertexSet.ncard - 1) Set.univ F ∧
      MinimumSpanningTreeValue G hG w F
end
end Specs.P205.Matroids.Prim
