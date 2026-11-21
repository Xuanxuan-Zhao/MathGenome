import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Foundations
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.VertexCover

/-! Independent interfaces for W49 and the following two paragraphs of paper.tex.
An edge is an unordered pair in `Sym2 V`; membership in the ambient edge set
ensures that its two endpoints differ. Matchings carry no isolated vertices.
The index `i` of a path edge is zero based. Augmenting paths have positive length,
so the requirement to begin and end with an edge outside the matching is substantive.
-/

universe u
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.Matching.Foundations

def IsMatchingType := ∀ {V : Type u} [Finite V],
  SimpleGraph V → Set (Sym2 V) → Prop

def IsMatchingValue : IsMatchingType := fun {_} _ G M =>
  M ⊆ G.edgeSet ∧ ∀ e ∈ M, ∀ f ∈ M, ∀ v : _, v ∈ e → v ∈ f → e = f

def EdgeMatchingType := ∀ {V : Type u} [Finite V], SimpleGraph V → Type u

def EdgeMatchingValue : EdgeMatchingType := fun {_} _ G => {M // IsMatchingValue G M}

def SaturatedType := ∀ {V : Type u} [Finite V], Set (Sym2 V) → V → Prop

def SaturatedValue : SaturatedType := fun {_} _ M v => ∃ e ∈ M, v ∈ e

def IsPerfectMatchingType := ∀ {V : Type u} [Finite V],
  SimpleGraph V → Set (Sym2 V) → Prop

def IsPerfectMatchingValue : IsPerfectMatchingType := fun {_} _ G M =>
  IsMatchingValue G M ∧ ∀ v, SaturatedValue M v

def IsVertexCoverType := ∀ {V : Type u} [Finite V], SimpleGraph V → Set V → Prop

def IsVertexCoverValue : IsVertexCoverType := fun {_} _ G C =>
  ∀ e ∈ G.edgeSet, ∃ v ∈ C, v ∈ e

def IsAugmentingPathType := ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  Set (Sym2 V) → ∀ {a b : V}, G.Walk a b → Prop

def IsAugmentingPathValue : IsAugmentingPathType := fun {_} _ G M {a b} p =>
  IsMatchingValue G M ∧ p.IsPath ∧ 0 < p.length ∧
  ¬ SaturatedValue M a ∧ ¬ SaturatedValue M b ∧
  (∀ i < p.length, s(p.getVert i, p.getVert (i + 1)) ∈ M ↔ i % 2 = 1) ∧
  s(p.getVert (p.length - 1), b) ∉ M

/-- The subgraph supported on the endpoints of an edge subset. -/
def edgeSubgraphType := ∀ {V : Type u} [Finite V] (G : SimpleGraph V)
  (M : Set (Sym2 V)), M ⊆ G.edgeSet → G.Subgraph

def edgeSubgraphValue : edgeSubgraphType := fun {_} _ G M h => {
  verts := {v | SaturatedValue M v}
  Adj := fun a b => s(a, b) ∈ M
  adj_sub := fun {_ _} hab => h hab
  edge_vert := fun {a b} hab => ⟨s(a, b), hab, Sym2.mem_mk_left a b⟩
  symm := ⟨fun a b hab => by simpa only [Sym2.eq_swap] using hab⟩ }

def saturated_iff_neighborType : Prop :=
  ∀ {V : Type u} [Finite V] (M : Set (Sym2 V)) (v : V),
  SaturatedValue M v ↔ ∃ w, s(v, w) ∈ M

def matching_iff_neighborsType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (M : Set (Sym2 V)),
  IsMatchingValue G M ↔ M ⊆ G.edgeSet ∧
    ∀ a b c : V, s(a, b) ∈ M → s(a, c) ∈ M → b = c

def edgeSubgraph_edgeSetType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (M : Set (Sym2 V))
  (h : M ⊆ G.edgeSet), (edgeSubgraphValue G M h).edgeSet = M

/-- The vertex-set condition is essential: Mathlib excludes isolated vertices
from a matching subgraph. -/
def matching_subgraph_iffType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (H : G.Subgraph),
  H.IsMatching ↔ IsMatchingValue G H.edgeSet ∧
    H.verts = {v | SaturatedValue H.edgeSet v}

def edgeSubgraph_isMatchingType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (M : Set (Sym2 V))
  (h : M ⊆ G.edgeSet), (edgeSubgraphValue G M h).IsMatching ↔ IsMatchingValue G M

def perfect_subgraph_iffType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (H : G.Subgraph),
  H.IsPerfectMatching ↔ IsPerfectMatchingValue G H.edgeSet

def vertexCover_mathlibType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (C : Set V),
  IsVertexCoverValue G C ↔ G.IsVertexCover C

def empty_matchingType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V), IsMatchingValue G ∅

def empty_perfectType : Prop :=
  ∀ {V : Type u} [Finite V] [IsEmpty V] (G : SimpleGraph V),
  IsPerfectMatchingValue G ∅

/-- Each matching edge has its own covered endpoint. -/
def covered_endpoint_injectionType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (M : Set (Sym2 V)) (C : Set V),
  IsMatchingValue G M → IsVertexCoverValue G C →
    ∃ f : M → C, Function.Injective f ∧ ∀ e : M, (f e).val ∈ e.val

def matching_le_coverType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (M : Set (Sym2 V)) (C : Set V),
  IsMatchingValue G M → IsVertexCoverValue G C → Nat.card M ≤ Nat.card C

end Specs.FiniteCombinatorics.Graph.Matching.Foundations
