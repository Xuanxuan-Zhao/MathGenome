import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Foundations
import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat

/-! Deletion minima in paper.tex, Corollary p204:whitney.
Vertex deletion uses the induced graph on the complement. Edge deletion
removes genuine edges and retains every vertex. The natural-number infimum
is a minimum whenever a cut exists (in particular for order at least two).
The empty deletion set realizes both minima on disconnected graphs. -/

universe u
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.Connectivity.Whitney

def VertexCutType := ∀ {V : Type u} [Finite V], SimpleGraph V → Set V → Prop
def VertexCutValue : VertexCutType := fun {_} _ G s =>
  ¬(G.induce sᶜ).Connected ∨ sᶜ.ncard = 1

def EdgeCutType := ∀ {V : Type u} [Finite V], SimpleGraph V → Set (Sym2 V) → Prop
def EdgeCutValue : EdgeCutType := fun {_} _ G s =>
  s ⊆ G.edgeSet ∧ ¬(G.deleteEdges s).Connected

def connectivityType := ∀ {V : Type u} [Finite V], SimpleGraph V → ℕ
def vertexConnectivityValue : connectivityType := fun {_} _ G =>
  sInf {k | ∃ s, VertexCutValue G s ∧ s.ncard = k}
def edgeConnectivityValue : connectivityType := fun {_} _ G =>
  sInf {k | ∃ s, EdgeCutValue G s ∧ s.ncard = k}
def minimumDegreeValue : connectivityType := fun {_} _ G =>
  sInf (Set.range (fun v => Nat.card (G.neighborSet v)))

def vertex_minimumType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V), 2 ≤ Nat.card V →
    ∃ s, VertexCutValue G s ∧ s.ncard = vertexConnectivityValue G ∧
      ∀ t, VertexCutValue G t → vertexConnectivityValue G ≤ t.ncard

def edge_minimumType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V), 2 ≤ Nat.card V →
    ∃ s, EdgeCutValue G s ∧ s.ncard = edgeConnectivityValue G ∧
      ∀ t, EdgeCutValue G t → edgeConnectivityValue G ≤ t.ncard

def degree_minimumType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V), 2 ≤ Nat.card V →
    ∃ v, Nat.card (G.neighborSet v) = minimumDegreeValue G ∧
      ∀ w, minimumDegreeValue G ≤ Nat.card (G.neighborSet w)

def disconnected_valuesType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V), ¬G.Connected →
    vertexConnectivityValue G = 0 ∧ edgeConnectivityValue G = 0

def whitney_boundsType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V), 2 ≤ Nat.card V →
    vertexConnectivityValue G ≤ edgeConnectivityValue G ∧
      edgeConnectivityValue G ≤ minimumDegreeValue G

def complete_vertexConnectivityType : Prop :=
  ∀ {V : Type u} [Finite V], 2 ≤ Nat.card V →
    vertexConnectivityValue (⊤ : SimpleGraph V) = Nat.card V - 1

end Specs.FiniteCombinatorics.Graph.Connectivity.Whitney
