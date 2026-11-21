import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.SetTheory.Cardinal.Finite

/-! The finite simple undirected graph conventions of paper.tex, W35.
All expected propositions and definition values below are independent of the implementation.
Edges in `Sym2` are identified with their unordered two-element endpoint subsets.
Walks and paths include the length-zero walk at a vertex. -/

universe u

noncomputable section

namespace Specs.FiniteCombinatorics.Graph.Foundations

def FiniteGraphType := ∀ (V : Type u) [Finite V], Type u

def FiniteGraphValue : FiniteGraphType := fun V _ => SimpleGraph V

def edgeSubsetsType := ∀ {V : Type u} [Finite V] [DecidableEq V], SimpleGraph V → Set (Finset V)

def edgeSubsetsValue : edgeSubsetsType := fun {_} _ _ G => Sym2.toFinset '' G.edgeSet

def SubgraphType := ∀ {V : Type u} [Finite V], SimpleGraph V → Type u

def SubgraphValue : SubgraphType := fun {_} _ G => G.Subgraph

def inducedType := ∀ {V : Type u} [Finite V], SimpleGraph V → (s : Set V) → SimpleGraph s

def inducedValue : inducedType := fun {_} _ G s => G.induce s

def degreeType := ∀ {V : Type u} [Finite V], SimpleGraph V → V → ℕ

def degreeValue : degreeType := fun {_} _ G v => Nat.card (G.neighborSet v)

def WalkOfLengthType := ∀ {V : Type u} [Finite V], (G : SimpleGraph V) → V → V → ℕ → Type u

def WalkOfLengthValue : WalkOfLengthType := fun {_} _ G a b k => {p : G.Walk a b // p.length = k}

def PathType := ∀ {V : Type u} [Finite V], (G : SimpleGraph V) → V → V → Type u

def PathValue : PathType := fun {_} _ G a b => G.Path a b

def CycleType := ∀ {V : Type u} [Finite V], (G : SimpleGraph V) → V → Type u

def CycleValue : CycleType := fun {_} _ G a => {p : G.Walk a a // p.IsCycle}

def ForestType := ∀ {V : Type u} [Finite V], SimpleGraph V → Prop

def ForestValue : ForestType := fun {_} _ G => G.IsAcyclic

def TreeType := ∀ {V : Type u} [Finite V], SimpleGraph V → Prop

def TreeValue : TreeType := fun {_} _ G => G.IsTree

def ComponentType := ∀ {V : Type u} [Finite V], SimpleGraph V → Type u

def ComponentValue : ComponentType := fun {_} _ G => G.ConnectedComponent

def componentCountType := ∀ {V : Type u} [Finite V], SimpleGraph V → ℕ

def componentCountValue : componentCountType := fun {_} _ G => Nat.card G.ConnectedComponent

def edge_subsets_iffType : Prop :=
  ∀ {V : Type u} [Finite V] [DecidableEq V] (G : SimpleGraph V) (s : Finset V),
  s ∈ edgeSubsetsValue G ↔ ∃ a b : V, G.Adj a b ∧ s = {a, b}

def edge_subsets_cardType : Prop :=
  ∀ {V : Type u} [Finite V] [DecidableEq V] (G : SimpleGraph V) (s : Finset V),
  s ∈ edgeSubsetsValue G → s.card = 2

def edge_membershipType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (a b : V),
  s(a, b) ∈ G.edgeSet ↔ G.Adj a b

def subgraph_interfaceType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (H : G.Subgraph) (a b : V),
  H.Adj a b → G.Adj a b ∧ a ∈ H.verts ∧ b ∈ H.verts

def induced_adjacencyType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (s : Set V) (a b : s),
  (G.induce s).Adj a b ↔ G.Adj a.val b.val

def degree_mathlibType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (v : V)
  [Fintype (G.neighborSet v)], degreeValue G v = G.degree v

def walk_supportType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (a b : V) (p : G.Walk a b),
  p.support.length = p.length + 1 ∧ p.support.IsChain G.Adj

def walk_endpointsType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (a b : V) (p : G.Walk a b),
  p.support.head p.support_ne_nil = a ∧ p.support.getLast p.support_ne_nil = b

def walk_from_sequenceType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (l : List V)
  (hne : l ≠ []) (_h : l.IsChain G.Adj),
  ∃ p : G.Walk (l.head hne) (l.getLast hne), p.support = l ∧ p.length = l.length - 1

def path_iffType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (a b : V) (p : G.Walk a b),
  p.IsPath ↔ p.support.Nodup

def cycle_iffType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (a : V) (p : G.Walk a a),
  p.IsCycle ↔ 3 ≤ p.length ∧ p.support.dropLast.Nodup

def reachability_equivalenceType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V), Equivalence G.Reachable

def walk_to_pathType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (a b : V) (p : G.Walk a b),
  ∃ q : G.Walk a b, q.IsPath ∧ q.length ≤ p.length ∧ List.Sublist q.support p.support

def reachable_iff_pathType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (a b : V),
  G.Reachable a b ↔ Nonempty (G.Path a b)

def component_eq_iffType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (a b : V),
  G.connectedComponentMk a = G.connectedComponentMk b ↔ G.Reachable a b

def connected_iff_pathsType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  G.Connected ↔ Nonempty V ∧ ∀ a b : V, Nonempty (G.Path a b)

def connected_iff_one_componentType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  G.Connected ↔ componentCountValue G = 1

def empty_componentsType : Prop :=
  ∀ {V : Type u} [Finite V] [IsEmpty V] (G : SimpleGraph V),
  componentCountValue G = 0

def empty_no_walkType : Prop :=
  ∀ {V : Type u} [Finite V] [IsEmpty V] (G : SimpleGraph V),
  ¬ ∃ (a b : V), Nonempty (G.Walk a b)

def empty_not_connectedType : Prop :=
  ∀ {V : Type u} [Finite V] [IsEmpty V] (G : SimpleGraph V), ¬G.Connected

def zero_length_pathType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (a : V),
  (SimpleGraph.Walk.nil : G.Walk a a).IsPath ∧
    (SimpleGraph.Walk.nil : G.Walk a a).length = 0

def forest_iff_no_cycleType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  ForestValue G ↔ ∀ a : V, ∀ p : G.Walk a a, ¬ p.IsCycle

def tree_iffType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  TreeValue G ↔ G.Connected ∧ ForestValue G

end Specs.FiniteCombinatorics.Graph.Foundations
