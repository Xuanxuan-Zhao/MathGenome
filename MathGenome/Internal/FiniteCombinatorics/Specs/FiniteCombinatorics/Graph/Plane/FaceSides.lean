import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Plane.Foundations
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! The shared numerical conclusion of the directed-side argument in
paper.tex, W62, lines 2410–2436. Faces are the actual connected components
of the sphere complement defined by `Foundations.Face`.

This is an expected proposition, not an assumed theorem. The drawing has
only the polygonal embedding hypotheses of the source. In particular, no
rotation system, side-to-face assignment, face finiteness, disk-face
condition or numerical face bound is supplied as a hypothesis. Any such
auxiliary data used in the proof must be constructed from the drawing.
Both sides of a bridge count even when they belong to the same face.
-/

universe u

namespace Specs.FiniteCombinatorics.Graph.Plane.FaceSides
open Specs.FiniteCombinatorics.Graph.Plane.Foundations

/-- For a connected simple polygonal drawing with at least three vertices,
every actual face has at least three directed sides, and at least four
when the graph is bipartite. The inequalities use the actual face count;
the general finiteness of that count is separately allocated to Euler. -/
def face_boundsType : Prop :=
  ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (D : Drawing G),
    G.Connected → 3 ≤ Nat.card V →
      3 * Nat.card (Face D) ≤ 2 * Nat.card G.edgeSet ∧
      (G.IsBipartite → 4 * Nat.card (Face D) ≤ 2 * Nat.card G.edgeSet)

end Specs.FiniteCombinatorics.Graph.Plane.FaceSides
