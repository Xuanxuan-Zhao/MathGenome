import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlaneTurningData
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PolygonTurning

/-!
The transverse-collar alternative for the inscribed-polygon reduction in
paper.tex 4851–4874. All vertices are the shared literal sampled vertices.
The collar and graph certificates are conclusions, not curve hypotheses.
-/
noncomputable section
open Set
open scoped ContDiff

namespace P202Specs.FineInscribedCollarGraphs
open PlanarRegionTopology (Plane ParameterCircle RegularJordanCurve realLift)
open PlaneTurning

/-- An actual affine ambient bicollar, transverse in the specified orientation.
No smoothness is demanded at the original finite joins. -/
structure TransverseCollar (c : RegularJordanCurve)
    (o : Orientation ℝ Plane (Fin 2)) where
  field : C(ParameterCircle, Plane)
  width : ℝ
  chart : OpenPartialHomeomorph (ParameterCircle × ℝ) Plane
  width_pos : 0 < width
  source_eq : chart.source = univ ×ˢ Ioo (-width) width
  formula : ∀ z, chart z = c.parametrization z.1 + z.2 • field z.1
  smooth_transverse : ∀ t : ℝ, (t : ParameterCircle) ∉ c.joins →
    ContDiffAt ℝ ∞ (realLift field) t ∧
      0 < inner ℝ (field (t : ParameterCircle))
        (o.rightAngleRotation (deriv (realLift c.parametrization) t))

/-- The graph and edge sign refer to this very chart and its inverse. -/
def IsPolygonGraph {c : RegularJordanCurve} {o : Orientation ℝ Plane (Fin 2)}
    (D : TransverseCollar c o) (Q : Partition) : Prop :=
  let p : Polygon Plane Q.count := Polygon.mk (inscribedVertex c Q)
  (∃ f : C(ParameterCircle, ℝ), (∀ q, |f q| < D.width / 4) ∧
    p.boundary ℝ = range (fun q => D.chart (q, f q))) ∧
  ∀ (i : Fin Q.count) (t : ℝ), t ∈ Ioo (0 : ℝ) 1 →
    0 < inner ℝ (D.field ((D.chart.symm (p.edgePath ℝ i t)).1))
      (o.rightAngleRotation (PolygonTurning.edgeVector p i))

/-- Local joint positivity for a varying fiber direction and two ordered
curve parameters; both sides of a join are included. -/
def LocallyPositiveSecants (c : RegularJordanCurve)
    (o : Orientation ℝ Plane (Fin 2)) (W : C(ParameterCircle, Plane)) : Prop :=
  ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ Icc (t - ε) (t + ε),
    ∀ s ∈ Icc (t - ε) (t + ε), ∀ u ∈ Icc (t - ε) (t + ε), s < u →
      0 < inner ℝ (W (q : ParameterCircle)) (o.rightAngleRotation
        (realLift c.parametrization u - realLift c.parametrization s))

/-- Actual inverse coordinates and transversality along every closed edge.
These are derived estimates, with no assumption of a global polygon graph. -/
def ControlledEdges {c : RegularJordanCurve} {o : Orientation ℝ Plane (Fin 2)}
    (D : TransverseCollar c o) (Q : Partition) : Prop :=
  let p : Polygon Plane Q.count := Polygon.mk (inscribedVertex c Q)
  ∀ (i : Fin Q.count) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
    p.edgePath ℝ i t ∈ D.chart.target ∧
    |(D.chart.symm (p.edgePath ℝ i t)).2| < D.width / 4 ∧
    0 < inner ℝ (D.field ((D.chart.symm (p.edgePath ℝ i t)).1))
      (o.rightAngleRotation (PolygonTurning.edgeVector p i))

namespace Expected

def collarExists : Prop := ∀ (c : RegularJordanCurve)
  (o : Orientation ℝ Plane (Fin 2)), Nonempty (TransverseCollar c o)

def collarWithLocalSecants : Prop := ∀ (c : RegularJordanCurve)
    (o : Orientation ℝ Plane (Fin 2)),
  ∃ D : TransverseCollar c o, LocallyPositiveSecants c o D.field

/-- A stronger, non-refinement-dependent estimate at every point of every edge.
The global graph equality remains a separate obligation in `fineGraphs`. -/
def fineEdgeControl : Prop := ∀ (c : RegularJordanCurve)
    (o : Orientation ℝ Plane (Fin 2)),
  ∃ D : TransverseCollar c o, ∃ δ : ℝ, 0 < δ ∧
    ∀ Q : Partition, Q.MeshLT δ → ControlledEdges D Q

/-- Complete assigned statement: every refining sufficiently fine partition,
including extra smooth vertices and the closing edge across the parameter cut. -/
def fineGraphs : Prop := ∀ (c : RegularJordanCurve)
    (o : Orientation ℝ Plane (Fin 2)) (A : ArcPresentation c),
  ∃ D : TransverseCollar c o, ∃ δ : ℝ, 0 < δ ∧
    ∀ Q : Partition, Q.Refines A → Q.MeshLT δ → IsPolygonGraph D Q

end Expected
end P202Specs.FineInscribedCollarGraphs
