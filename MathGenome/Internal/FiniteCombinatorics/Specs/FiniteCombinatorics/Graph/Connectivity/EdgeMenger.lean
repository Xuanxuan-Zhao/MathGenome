import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Foundations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Dart
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Flows.Foundations

/-! Independent statement of the edge assertion of paper.tex W48 (1708–1749).
The graph is finite, simple and undirected. Only distinctness of the endpoints
is assumed; in particular adjacent endpoints are allowed. Families are lists of
actual vertex-simple paths, and disjointness refers to unordered graph edges.
The empty family and empty separator express the disconnected case. -/

universe u
noncomputable section
namespace FiniteCombinatorics.Graph.EdgeMenger
variable {V : Type u} {G : SimpleGraph V} {s t : V}

/-- The unordered edges traversed by an undirected simple path. -/
def pathEdges (p : G.Path s t) : Finset (Sym2 V) := by
  classical
  exact p.val.edges.toFinset

/-- A finite family whose distinct occurrences have disjoint edge sets. -/
def Packing (ps : List (G.Path s t)) : Prop :=
  ps.Pairwise fun p q => Disjoint (pathEdges p) (pathEdges q)

/-- Only edges of G may be deleted, and deletion destroys reachability. -/
def Separator (G : SimpleGraph V) (s t : V) (F : Finset (Sym2 V)) : Prop :=
  (↑F : Set (Sym2 V)) ⊆ G.edgeSet ∧ ¬ (G.deleteEdges (↑F : Set (Sym2 V))).Reachable s t

section Network
open scoped Classical
variable [Fintype V]

/-- Replace each edge by its two oriented darts. -/
def dartGraph (G : SimpleGraph V) : Directed.Digraph V G.Dart :=
  { tail := fun a => a.fst, head := fun a => a.snd }

/-- Both directions have unit capacity, with the original distinct endpoints. -/
def unitNetwork (G : SimpleGraph V) (s t : V) (hst : s ≠ t) : Flows.Network V G.Dart :=
  { graph := dartGraph G
    capacity := fun _ => 1
    capacity_nonneg := fun _ => zero_le_one
    source := s
    sink := t
    source_ne_sink := hst }

/-- Edges with one endpoint on each side, represented once as unordered edges. -/
def boundary (G : SimpleGraph V) (S : Set V) : Finset (Sym2 V) :=
  (Finset.univ.filter (fun a : G.Dart => a.fst ∈ S ∧ a.snd ∉ S)).image
    SimpleGraph.Dart.edge

end Network

/-- Attainment, equality and both universal optimality conclusions. -/
def edge_menger_type : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (s t : V), s ≠ t →
    ∃ (ps : List (G.Path s t)) (F : Finset (Sym2 V)),
      Packing ps ∧ Separator G s t F ∧ ps.length = F.card ∧
      (∀ qs : List (G.Path s t), Packing qs → qs.length ≤ ps.length) ∧
      (∀ D : Finset (Sym2 V), Separator G s t D → F.card ≤ D.card)

/-- The already disconnected case has value zero on both sides. -/
def disconnected_type : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (s t : V), ¬ G.Reachable s t →
    Packing ([] : List (G.Path s t)) ∧ Separator G s t ∅ ∧
      (∀ ps : List (G.Path s t), Packing ps → ps.length = 0) ∧
      (∀ F : Finset (Sym2 V), Separator G s t F → 0 ≤ F.card)

/-- The elementary packing/separator inequality, with no adjacency restriction. -/
def packing_le_separator_type : Prop :=
  ∀ {V : Type u} (G : SimpleGraph V) (s t : V)
    (ps : List (G.Path s t)) (F : Finset (Sym2 V)),
    Packing ps → Separator G s t F → ps.length ≤ F.card

end FiniteCombinatorics.Graph.EdgeMenger
