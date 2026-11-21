import Mathlib.Combinatorics.Graph.Simple
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Set.Card
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Foundations

/-! Finite indexed undirected multigraphs. Ambient label types may be infinite;
only the actual vertex and edge sets must be finite. Edges remain elements of β.
The degree counts incident edge identities once and loops once more.
This is the convention for edge colorings (paper.tex, lines 2275–2283) and the
indexed graph convention preceding p204:W72 (paper.tex, lines 2938–2946).
`underlying` discards loops and multiplicities; it is only an adjacency shadow. -/

universe u v
noncomputable section

-- These are type abbreviations for interfaces with two independent label universes.
set_option linter.checkUnivs false

namespace Specs.FiniteCombinatorics.Graph.MultigraphFoundation

def IsFiniteType := ∀ {α : Type u} {β : Type v}, _root_.Graph α β → Prop

abbrev IsFiniteValue : IsFiniteType := fun G => G.vertexSet.Finite ∧ G.edgeSet.Finite

def FiniteIndexedGraphType := Type u → Type v → Type (max u v)

abbrev FiniteIndexedGraphValue : FiniteIndexedGraphType := fun α β => {G : _root_.Graph α β // IsFiniteValue G}

def VertexType := ∀ {α : Type u} {β : Type v}, _root_.Graph α β → Type u

abbrev VertexValue : VertexType := fun G => G.vertexSet

def EdgeType := ∀ {α : Type u} {β : Type v}, _root_.Graph α β → Type v

abbrev EdgeValue : EdgeType := fun G => G.edgeSet

def IncidenceType := ∀ {α : Type u} {β : Type v}, _root_.Graph α β → β → α → Prop

abbrev IncidenceValue : IncidenceType := fun G => G.Inc

def incidentEdgesType := ∀ {α : Type u} {β : Type v}, _root_.Graph α β → α → Set β

abbrev incidentEdgesValue : incidentEdgesType := fun G => G.incidenceSet

def loopEdgesType := ∀ {α : Type u} {β : Type v}, _root_.Graph α β → α → Set β

abbrev loopEdgesValue : loopEdgesType := fun G => G.loopSet

def degreeType := ∀ {α : Type u} {β : Type v}, _root_.Graph α β → α → ℕ

abbrev degreeValue : degreeType := fun G x => Nat.card (G.incidenceSet x) + Nat.card (G.loopSet x)

def LooplessType := ∀ {α : Type u} {β : Type v}, _root_.Graph α β → Prop

abbrev LooplessValue : LooplessType := fun G => G.Loopless

def SimpleType := ∀ {α : Type u} {β : Type v}, _root_.Graph α β → Prop

abbrev SimpleValue : SimpleType := fun G => G.Simple

def underlyingType := ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β), SimpleGraph (VertexValue G)

abbrev underlyingValue : underlyingType := fun G => G.toSimpleGraph

def ofSimpleGraphType := ∀ {α : Type u}, SimpleGraph α → _root_.Graph α (Sym2 α)

abbrev ofSimpleGraphValue : ofSimpleGraphType := fun G => _root_.Graph.ofSimpleGraph G

def finite_verticesType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β), IsFiniteValue G → Finite (VertexValue G)

def finite_edgesType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β), IsFiniteValue G → Finite (EdgeValue G)

def finite_incidentEdgesType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) (_h : IsFiniteValue G) (x : α), (incidentEdgesValue G x).Finite

def finite_loopEdgesType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) (_h : IsFiniteValue G) (x : α), (loopEdgesValue G x).Finite

def isLink_endpointsType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) (e : β) (x y : α), G.IsLink e x y → e ∈ G.edgeSet ∧ x ∈ G.vertexSet ∧ y ∈ G.vertexSet

def isLink_symmetryType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) (e : β) (x y : α), G.IsLink e x y ↔ G.IsLink e y x

def edge_iff_isLinkType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) (e : β), e ∈ G.edgeSet ↔ ∃ x y, G.IsLink e x y

def incidence_iffType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) (e : β) (x : α), IncidenceValue G e x ↔ ∃ y, G.IsLink e x y

def incidence_membershipType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) (e : β) (x : α), e ∈ incidentEdgesValue G x ↔ G.Inc e x

def loop_membershipType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) (e : β) (x : α), e ∈ loopEdgesValue G x ↔ G.IsLink e x x

def degree_formulaType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) (x : α), degreeValue G x = Nat.card (G.incidenceSet x) + Nat.card (G.loopSet x)

def degree_nonloop_and_loopsType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) (_h : IsFiniteValue G) (x : α), degreeValue G x = Nat.card {e : β // G.IsNonloopAt e x} + 2 * Nat.card (G.loopSet x)

def degree_looplessType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) [G.Loopless] (x : α), degreeValue G x = Nat.card (G.incidenceSet x)

def degree_outsideType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) (x : α), x ∉ G.vertexSet → degreeValue G x = 0

def underlying_adjacencyType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) (x y : VertexValue G), (underlyingValue G).Adj x y ↔ x ≠ y ∧ ∃ e : β, G.IsLink e x y

def underlying_loopless_adjacencyType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) [G.Loopless] (x y : VertexValue G), (underlyingValue G).Adj x y ↔ ∃ e : β, G.IsLink e x y

def simple_edge_uniqueType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) [G.Simple] (e f : β) (x y : α), G.IsLink e x y → G.IsLink f x y → e = f

def simple_incidence_bijectionType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) [G.Simple] (x : VertexValue G), ∃ f : G.incidenceSet x → (underlyingValue G).neighborSet x, Function.Bijective f ∧ ∀ e, G.IsLink e.val x.val (f e).val.val

def underlying_simple_adjacencyType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) [G.Simple] (x y : VertexValue G), (underlyingValue G).Adj x y ↔ ∃! e : β, G.IsLink e x y

def degree_simple_underlyingType : Prop :=
  ∀ {α : Type u} {β : Type v} (G : _root_.Graph α β) [G.Simple] (x : VertexValue G) [Fintype ((underlyingValue G).neighborSet x)], degreeValue G x = (underlyingValue G).degree x

def ofSimpleGraph_verticesType : Prop :=
  ∀ {α : Type u} (G : SimpleGraph α), (ofSimpleGraphValue G).vertexSet = Set.univ

def ofSimpleGraph_edgesType : Prop :=
  ∀ {α : Type u} (G : SimpleGraph α), (ofSimpleGraphValue G).edgeSet = G.edgeSet

def ofSimpleGraph_isLinkType : Prop :=
  ∀ {α : Type u} (G : SimpleGraph α) (e : Sym2 α) (x y : α), (ofSimpleGraphValue G).IsLink e x y ↔ e = s(x, y) ∧ G.Adj x y

def ofSimpleGraph_adjacencyType : Prop :=
  ∀ {α : Type u} (G : SimpleGraph α) (x y : α), (ofSimpleGraphValue G).Adj x y ↔ G.Adj x y

def ofSimpleGraph_incidenceType : Prop :=
  ∀ {α : Type u} (G : SimpleGraph α) (e : Sym2 α) (x : α), (ofSimpleGraphValue G).Inc e x ↔ e ∈ G.incidenceSet x

def ofSimpleGraph_simpleType : Prop :=
  ∀ {α : Type u} (G : SimpleGraph α), (ofSimpleGraphValue G).Simple

def ofSimpleGraph_finiteType : Prop :=
  ∀ {α : Type u} [Finite α] (G : SimpleGraph α), IsFiniteValue (ofSimpleGraphValue G)

def ofSimpleGraph_isoType : Prop :=
  ∀ {α : Type u} (G : SimpleGraph α), Nonempty ((underlyingValue (ofSimpleGraphValue G)) ≃g G)

def degree_ofSimpleGraphType : Prop :=
  ∀ {α : Type u} [Finite α] (G : SimpleGraph α) (x : α), degreeValue (ofSimpleGraphValue G) x = Specs.FiniteCombinatorics.Graph.Foundations.degreeValue G x

def degree_ofSimpleGraph_mathlibType : Prop :=
  ∀ {α : Type u} (G : SimpleGraph α) (x : α) [Fintype (G.neighborSet x)], degreeValue (ofSimpleGraphValue G) x = G.degree x

def banana_linksType : Prop :=
  ∀ {α : Type u} {β : Type v} (x y : α) (s : Set β) (e : β), (_root_.Graph.banana x y s).IsLink e x y ↔ e ∈ s

def banana_finiteType : Prop :=
  ∀ {α : Type u} {β : Type v} (x y : α) (s : Set β), s.Finite → IsFiniteValue (_root_.Graph.banana x y s)

def banana_degreeType : Prop :=
  ∀ {α : Type u} {β : Type v} (x y : α) (s : Set β), x ≠ y → degreeValue (_root_.Graph.banana x y s) x = Nat.card s

def loop_banana_degreeType : Prop :=
  ∀ {α : Type u} {β : Type v} (x : α) (s : Set β), degreeValue (_root_.Graph.banana x x s) x = 2 * Nat.card s

end Specs.FiniteCombinatorics.Graph.MultigraphFoundation
