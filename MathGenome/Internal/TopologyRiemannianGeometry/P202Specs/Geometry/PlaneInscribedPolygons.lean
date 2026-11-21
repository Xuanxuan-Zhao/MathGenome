import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlaneTurningData
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PolygonTurning

/-!
Independent interface for the inscribed-polygon reduction in paper.tex
4851–4874. The vertices are literal samples of the original parametrization.
No simplicity, orientation, integral, or collar certificate is in the input.
The mesh threshold is uniform over all knot-preserving partitions.
-/
noncomputable section
open Set
open scoped unitInterval

namespace P202Specs.PlaneTurning
open PlanarRegionTopology (Plane RegularJordanCurve)

/-- The polygon with the shared literal inscribed vertices. -/
def inscribedPolygon (c : RegularJordanCurve) (Q : Partition) : Polygon Plane Q.count :=
  ⟨inscribedVertex c Q⟩

namespace InscribedExpected

/-- Unconditional elementary geometry, including the cyclic closing edge. -/
def vertexGeometry : Prop := ∀ (c : RegularJordanCurve) (Q : Partition),
  Function.Injective (inscribedPolygon c Q).vertices ∧
    (inscribedPolygon c Q).HasNondegenerateEdges ∧
    (∀ i, PolygonTurning.edgeVector (inscribedPolygon c Q) i = inscribedEdge c Q i) ∧
    (∀ i (t : unitInterval),
      (inscribedPolygon c Q).edgePath ℝ i t = inscribedEdgeMap c Q i t) ∧
    (inscribedPolygon c Q).boundary ℝ = inscribedTrace c Q

/-- The full assigned result: every sufficiently fine refining partition
produces a simple noncuspidal polygon with its actual bounded side on the
left. Reflex and extra straight subdivision vertices are permitted. -/
def eventualGeometry : Prop := ∀ (c : RegularJordanCurve)
    (o : Orientation ℝ Plane (Fin 2)) (U : Set Plane),
  IsBoundedSide c U → HasBoundedSideOnLeft c o U →
  ∀ A : ArcPresentation c, ∃ δ : ℝ, 0 < δ ∧
    ∀ Q : Partition, Q.Refines A → Q.MeshLT δ →
      PolygonTurning.IsSimple (inscribedPolygon c Q) ∧
      PolygonTurning.Noncuspidal (inscribedPolygon c Q) ∧
      ∃ UQ : Set Plane,
        PolygonTurning.IsBoundedSide (inscribedPolygon c Q) UQ ∧
        PolygonTurning.HasBoundedSideOnLeft o (inscribedPolygon c Q) UQ

/-- The embedding part of the reduction holds for every fine partition,
independently of its smooth-presentation knots or bounded-side orientation. -/
def eventualEmbeddedGeometry : Prop := ∀ c : RegularJordanCurve,
  ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Partition, Q.MeshLT δ →
    PolygonTurning.IsSimple (inscribedPolygon c Q) ∧
    PolygonTurning.Noncuspidal (inscribedPolygon c Q)

/-- An edge of every sufficiently fine inscribed polygon meets the original
curve only on its own closed parameter arc, with the cyclic cut retained. -/
def eventualArcIsolation : Prop := ∀ c : RegularJordanCurve,
  ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Partition, Q.MeshLT δ →
    ∀ (i : Fin Q.count) (t : ℝ),
      PlanarRegionTopology.realLift c.parametrization t ∈
        (inscribedPolygon c Q).edgeSet ℝ i →
      ∃ k : ℤ, t + k ∈ Icc (Q.time i.castSucc) (Q.time i.succ)

/-- Uniform approximation at the affine edge parameter, proved without
any assertion that closeness alone preserves the bounded-side orientation. -/
def uniformApproximation : Prop := ∀ (c : RegularJordanCurve) (ε : ℝ), 0 < ε →
  ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Partition, Q.MeshLT δ →
    ∀ (i : Fin Q.count) (t : unitInterval),
      dist (inscribedEdgeMap c Q i t)
        (PlanarRegionTopology.realLift c.parametrization
          (Q.time i.castSucc + (Q.time i.succ - Q.time i.castSucc) * t)) < ε

/-- Intersecting short edges have nearby parameters in the circle metric,
including for edges adjacent to the parameter cut. -/
def intersectingEdgesLocalize : Prop := ∀ (c : RegularJordanCurve) (η : ℝ), 0 < η →
  ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Partition, Q.MeshLT δ →
    ∀ (i j : Fin Q.count) (s t : unitInterval),
      inscribedEdgeMap c Q i s = inscribedEdgeMap c Q j t →
      dist (Q.time i.castSucc : PlanarRegionTopology.ParameterCircle)
        (Q.time j.castSucc : PlanarRegionTopology.ParameterCircle) < η

/-- Eventual embedded polygons bound actual Jordan domains; the orientation
of that bounded domain remains a separate geometric assertion. -/
def eventualBoundedGeometry : Prop := ∀ c : RegularJordanCurve,
  ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Partition, Q.MeshLT δ →
    PolygonTurning.IsSimple (inscribedPolygon c Q) ∧
    PolygonTurning.Noncuspidal (inscribedPolygon c Q) ∧
    ∃ UQ : Set Plane, PolygonTurning.IsBoundedSide (inscribedPolygon c Q) UQ

/-- Every open neighborhood of the curve contains every sufficiently fine
literal polygon, uniformly over the partitions and their edge points. -/
def eventualNeighborhoodContainment : Prop := ∀ (c : RegularJordanCurve) (O : Set Plane),
  IsOpen O → c.trace ⊆ O →
  ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Partition, Q.MeshLT δ → inscribedTrace c Q ⊆ O

/-- For a simple polygon, inward rays transverse to each directed edge imply
the exact upstream left-normal test. No orientation is inferred from closeness. -/
def transverseRayCriterion : Prop := ∀ (n : ℕ) (p : Polygon Plane n)
    (o : Orientation ℝ Plane (Fin 2)) (U : Set Plane),
  PolygonTurning.IsSimple p → IsOpen U → frontier U = p.boundary ℝ →
  (∀ (i : Fin n) (t : ℝ), t ∈ Ioo (0 : ℝ) 1 →
    ∃ w : Plane, 0 < inner ℝ w (o.rightAngleRotation (PolygonTurning.edgeVector p i)) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
        p.edgePath ℝ i t + r • w ∈ U) →
  PolygonTurning.HasBoundedSideOnLeft o p U

/-- The two actual Jordan sides of an original curve have coherent opposite
normal signs, derived from the genuine bicollar rather than assumed. -/
def coherentJordanOrientation : Prop := ∀ (c : RegularJordanCurve) (A B : Set Plane),
  IsOpen A → IsOpen B → Disjoint A B → A ∪ B = c.traceᶜ →
  frontier A = c.trace → frontier B = c.trace →
  ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
    PlanarRegionTopology.HasSideOnLeft A c sign ∧
    PlanarRegionTopology.HasSideOnLeft B c (-sign)

end InscribedExpected
end P202Specs.PlaneTurning
