import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Foundations

/-! Independent statements for the forest count and bridge assertions of W38.
Deleting an edge retains the entire vertex type. -/
universe u
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.Trees.ForestsBridges
open Specs.FiniteCombinatorics.Graph.Foundations

def BridgeType := ∀ {V : Type u} [Finite V], SimpleGraph V → Sym2 V → Prop

def BridgeValue : BridgeType := fun {_} _ G e =>
  componentCountValue G < componentCountValue (G.deleteEdges {e})

def forest_edge_countType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V), ForestValue G →
    Nat.card G.edgeSet = Nat.card V - componentCountValue G

def bridge_iff_isBridgeType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (e : Sym2 V),
    e ∈ G.edgeSet → (BridgeValue G e ↔ G.IsBridge e)

def bridge_iff_no_cycleType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (e : Sym2 V),
    e ∈ G.edgeSet → (BridgeValue G e ↔
      ∀ (a : V) (p : G.Walk a a), p.IsCycle → e ∉ p.edges)

end Specs.FiniteCombinatorics.Graph.Trees.ForestsBridges
