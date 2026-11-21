import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Plane.Foundations
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! The edge bounds and nonplanarity conclusions of paper.tex, W62.
The graph is allowed to be disconnected, with isolated vertices and
single-edge components. Planarity uses the original polygonal drawings.
Since the vertex count is at least three, the natural subtractions below
express the same bounds as untruncated integer subtraction. -/

universe u
noncomputable section

namespace Specs.FiniteCombinatorics.Graph.Plane.EdgeBounds
open Specs.FiniteCombinatorics.Graph.Plane.Foundations

def planar_edge_boundType : Prop :=
  ∀ {V : Type u} [Finite V] {G : SimpleGraph V},
    Planar G → 3 ≤ Nat.card V → Nat.card G.edgeSet ≤ 3 * Nat.card V - 6

def planar_bipartite_edge_boundType : Prop :=
  ∀ {V : Type u} [Finite V] {G : SimpleGraph V},
    Planar G → 3 ≤ Nat.card V → G.IsBipartite →
      Nat.card G.edgeSet ≤ 2 * Nat.card V - 4

def complete_five_nonplanarType : Prop :=
  ¬Planar (⊤ : SimpleGraph (Fin 5))

def complete_three_three_nonplanarType : Prop :=
  ¬Planar (completeBipartiteGraph (Fin 3) (Fin 3))

end Specs.FiniteCombinatorics.Graph.Plane.EdgeBounds
