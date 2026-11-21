import Mathlib.Geometry.Polygon.Basic
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Normed.Module.Ray
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Data.Fin.Rev

/-!
The discrete stage of paper.tex 4885–4916, within the complete turning
lemma at 4830–4916. These definitions describe actual straight polygons;
neither a triangulation, a winding number, nor an angle-sum certificate
is part of the input. In particular, consecutive collinear edges pointing
in the same direction are allowed, as are reflex vertices.

The plane and its orientation are arbitrary. The bounded domain is supplied
as a set with its geometric defining properties, not with any homology or
triangulation assumptions. `HasBoundedSideOnLeft` uses the actual quarter
turn of each directed edge at every point of its relative interior.
-/

noncomputable section
open Set
open scoped BigOperators

universe u
namespace P202Specs.PolygonTurning

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {n : ℕ}

/-- The outgoing directed edge vector at vertex `i`. -/
def edgeVector (p : Polygon V n) (i : Fin n) : V :=
  p (finRotate n i) - p i

/-- The directed edge arriving at vertex `i`. -/
def incomingVector (p : Polygon V n) (i : Fin n) : V :=
  edgeVector p ((finRotate n).symm i)

/-- Simplicity excludes crossings, overlap, repeated vertices, and a vertex
on the interior of a different edge. Adjacent edges may meet at their shared
endpoint. No affine independence of successive triples is imposed. -/
def IsSimple (p : Polygon V n) : Prop :=
  3 ≤ n ∧ Function.Injective p.vertices ∧ p.HasNondegenerateEdges ∧
    ∀ i j : Fin n, i ≠ j →
      Disjoint (openSegment ℝ (p i) (p (finRotate n i))) (p.edgeSet ℝ j)

/-- The two consistently directed one-sided unit tangents are not opposite.
This condition places no sign restriction on the exterior angle. -/
def Noncuspidal (p : Polygon V n) : Prop :=
  ∀ i : Fin n,
    NormedSpace.normalize (incomingVector p i) ≠
      -NormedSpace.normalize (edgeVector p i)

/-- Geometric description of the bounded Jordan side. Nonemptiness is part
of `IsConnected`; the boundary is the literal union of straight edges. -/
def IsBoundedSide (p : Polygon V n) (U : Set V) : Prop :=
  IsOpen U ∧ IsConnected U ∧ Bornology.IsBounded U ∧ frontier U = p.boundary ℝ

variable [Fact (Module.finrank ℝ V = 2)]

/-- Small translations to the left of every directed edge enter the bounded
side. Vertices themselves are excluded from this smooth-arc test. -/
def HasBoundedSideOnLeft (o : Orientation ℝ V (Fin 2)) (p : Polygon V n)
    (U : Set V) : Prop :=
  ∀ (i : Fin n) (t : ℝ), t ∈ Ioo (0 : ℝ) 1 →
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      p.edgePath ℝ i t + r • o.rightAngleRotation (edgeVector p i) ∈ U

/-- The shorter signed rotation from the incoming direction to the outgoing
direction, with values in (-π,π] (and in (-π,π) under noncuspidality).
For a positively oriented polygon it is π minus the interior angle,
including at a reflex vertex. -/
def exteriorAngle (o : Orientation ℝ V (Fin 2)) (p : Polygon V n)
    (i : Fin n) : ℝ :=
  (o.oangle (incomingVector p i) (edgeVector p i)).toReal

def totalTurning (o : Orientation ℝ V (Fin 2)) (p : Polygon V n) : ℝ :=
  ∑ i, exteriorAngle o p i

/-- The same polygon with its vertex order reversed, hence with its actual
edge directions reversed. This is not a separately supplied direction loop. -/
def reverse (p : Polygon V n) : Polygon V n := ⟨p.vertices ∘ Fin.rev⟩

namespace Expected

/-- Complete simple-polygon turning conclusion, with the reversal value.
No triangulation, homological finiteness, or angle accounting is assumed. -/
def turning : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = 2)] (n : ℕ) (p : Polygon V n)
    (o : Orientation ℝ V (Fin 2)) (U : Set V),
    IsSimple p → Noncuspidal p → IsBoundedSide p U →
    HasBoundedSideOnLeft o p U →
      totalTurning o p = 2 * Real.pi ∧ totalTurning o (reverse p) = -(2 * Real.pi)

/-- Reversing traversal negates the real signed turning sum, with the
noncuspidality needed to avoid the π branch cut. -/
def reversal : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = 2)] (n : ℕ) (p : Polygon V n)
    (o : Orientation ℝ V (Fin 2)),
    p.HasNondegenerateEdges → Noncuspidal p →
      totalTurning o (reverse p) = -totalTurning o p

end Expected
end P202Specs.PolygonTurning
