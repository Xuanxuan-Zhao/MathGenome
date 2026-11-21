import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.MultigraphFoundation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat

/-! The edge-coloring conventions preceding paper.tex, W61.
Palettes are `Fin k`, including the empty palette. Edge identities are the
actual indexed edges, not pairs of endpoints. Only distinct edges must differ.
The degree lower bounds require looplessness; no degree is lost to simplification.
All specifications are independent of the candidate implementation. -/

universe u v
noncomputable section
set_option linter.checkUnivs false
namespace Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations


def ColoringType := ∀ {α : Type u} {β : Type v}, _root_.Graph α β → ℕ → Type v

abbrev ColoringValue : ColoringType :=
  fun {α} {_} G k => {c : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.EdgeValue G → Fin k //
    ∀ (e f : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.EdgeValue G), e ≠ f →
      (∃ x : α, G.Inc e.val x ∧ G.Inc f.val x) → c e ≠ c f}

def ColorableType := ∀ {α : Type u} {β : Type v}, _root_.Graph α β → ℕ → Prop

abbrev ColorableValue : ColorableType :=
  fun G k => Nonempty (ColoringValue G k)

def chromaticIndexType := ∀ {α : Type u} {β : Type v}, _root_.Graph α β → ℕ

abbrev chromaticIndexValue : chromaticIndexType :=
  fun G => sInf {k : ℕ | ColorableValue G k}

def maximumDegreeType := ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β), Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G → ℕ

abbrev maximumDegreeValue : maximumDegreeType :=
  fun G h => h.1.toFinset.sup (Specs.FiniteCombinatorics.Graph.MultigraphFoundation.degreeValue G)

def SimpleColoringType := ∀ {V : Type u}, SimpleGraph V → ℕ → Type u

abbrev SimpleColoringValue : SimpleColoringType :=
  fun G k => ColoringValue (Specs.FiniteCombinatorics.Graph.MultigraphFoundation.ofSimpleGraphValue G) k

def SimpleColorableType := ∀ {V : Type u}, SimpleGraph V → ℕ → Prop

abbrev SimpleColorableValue : SimpleColorableType :=
  fun G k => Nonempty (SimpleColoringValue G k)

def simpleChromaticIndexType := ∀ {V : Type u}, SimpleGraph V → ℕ

abbrev simpleChromaticIndexValue : simpleChromaticIndexType :=
  fun G => chromaticIndexValue (Specs.FiniteCombinatorics.Graph.MultigraphFoundation.ofSimpleGraphValue G)

def simpleMaximumDegreeType := ∀ {V : Type u} [Finite V], SimpleGraph V → ℕ

abbrev simpleMaximumDegreeValue : simpleMaximumDegreeType :=
  fun {V} _ G => (Set.toFinite (Set.univ : Set V)).toFinset.sup (fun x => Nat.card (G.neighborSet x))

def colorable_distinct_edgesType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β),
    Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G → ColorableValue G (Nat.card (Specs.FiniteCombinatorics.Graph.MultigraphFoundation.EdgeValue G))

def colorable_existsType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β),
    Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G → ∃ k, ColorableValue G k

def colorable_monoType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) {k l : ℕ},
    k ≤ l → ColorableValue G k → ColorableValue G l

def chromaticIndex_attainedType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β),
    Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G → ColorableValue G (chromaticIndexValue G)

def chromaticIndex_leType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) {k : ℕ},
    ColorableValue G k → chromaticIndexValue G ≤ k

def colorable_iff_chromaticIndex_leType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β),
    Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G → ∀ k, ColorableValue G k ↔ chromaticIndexValue G ≤ k

def colorable_zero_iffType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β),
    ColorableValue G 0 ↔ G.edgeSet = ∅

def chromaticIndex_zero_iffType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β),
    Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G → (chromaticIndexValue G = 0 ↔ G.edgeSet = ∅)

def degree_le_colorsType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) [G.Loopless]
    {k : ℕ}, ColorableValue G k → ∀ x : α, Specs.FiniteCombinatorics.Graph.MultigraphFoundation.degreeValue G x ≤ k

def maximumDegree_le_colorsType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) [G.Loopless]
    (h : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G) {k : ℕ}, ColorableValue G k → maximumDegreeValue G h ≤ k

def maximumDegree_le_chromaticIndexType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) [G.Loopless]
    (h : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G), maximumDegreeValue G h ≤ chromaticIndexValue G

def degree_le_maximumDegreeType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β)
    (h : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G) (x : α), Specs.FiniteCombinatorics.Graph.MultigraphFoundation.degreeValue G x ≤ maximumDegreeValue G h

def maximumDegree_empty_verticesType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β)
    (h : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue G), G.vertexSet = ∅ → maximumDegreeValue G h = 0

def simple_coloring_iffType : Prop :=
  ∀ {V : Type u} (G : SimpleGraph V) (k : ℕ) (c : G.edgeSet → Fin k),
    (∀ (e f : G.edgeSet), e ≠ f →
      (∃ x : V, e.val ∈ G.incidenceSet x ∧ f.val ∈ G.incidenceSet x) → c e ≠ c f) ↔
    ∃ C : SimpleColoringValue G k, C.val = c

def simple_colorable_iffType : Prop :=
  ∀ {V : Type u} (G : SimpleGraph V) (k : ℕ),
    SimpleColorableValue G k ↔ ColorableValue (Specs.FiniteCombinatorics.Graph.MultigraphFoundation.ofSimpleGraphValue G) k

def simple_colorable_distinct_edgesType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    SimpleColorableValue G (Nat.card G.edgeSet)

def simple_chromaticIndex_attainedType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    SimpleColorableValue G (simpleChromaticIndexValue G)

def simple_colorable_iff_chromaticIndex_leType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (k : ℕ),
    SimpleColorableValue G k ↔ simpleChromaticIndexValue G ≤ k

def simple_chromaticIndex_zero_iffType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    simpleChromaticIndexValue G = 0 ↔ G.edgeSet = ∅

def maximumDegree_ofSimpleGraphType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V)
    (h : Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue (Specs.FiniteCombinatorics.Graph.MultigraphFoundation.ofSimpleGraphValue G)),
    maximumDegreeValue (Specs.FiniteCombinatorics.Graph.MultigraphFoundation.ofSimpleGraphValue G) h = simpleMaximumDegreeValue G

def simple_degree_le_chromaticIndexType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (x : V),
    Nat.card (G.neighborSet x) ≤ simpleChromaticIndexValue G

def simple_maximumDegree_le_chromaticIndexType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    simpleMaximumDegreeValue G ≤ simpleChromaticIndexValue G

def simple_maximumDegree_emptyType : Prop :=
  ∀ {V : Type u} [Finite V] [IsEmpty V] (G : SimpleGraph V),
    simpleMaximumDegreeValue G = 0

def simple_maximumDegree_mathlibType : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj], simpleMaximumDegreeValue G = G.maxDegree

end Specs.FiniteCombinatorics.Graph.EdgeColoring.Foundations
