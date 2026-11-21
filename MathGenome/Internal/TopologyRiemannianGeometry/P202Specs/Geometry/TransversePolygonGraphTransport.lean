import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlaneTurningData
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PolygonTurning

/-! Bounded-side orientation transport for an actual transverse collar graph.
The graph and all edge-interior transversality tests are inputs; neither a
polygon side, its orientation, nor an ambient isotopy is assumed. -/
noncomputable section
open Set
open scoped ContDiff
namespace P202Specs.TransversePolygonGraphTransport
open PlanarRegionTopology (Plane ParameterCircle RegularJordanCurve realLift)

namespace Expected

def transport : Prop :=
  ∀ (c : RegularJordanCurve) (o : Orientation ℝ Plane (Fin 2)) (U : Set Plane),
    PlaneTurning.IsBoundedSide c U → PlaneTurning.HasBoundedSideOnLeft c o U →
    ∀ (W : C(ParameterCircle, Plane)) (a : ℝ), 0 < a →
    ∀ e : OpenPartialHomeomorph (ParameterCircle × ℝ) Plane,
      e.source = univ ×ˢ Ioo (-a) a →
      (∀ (q : ParameterCircle) (r : ℝ), e (q, r) = c.parametrization q + r • W q) →
      (∀ t : ℝ, (t : ParameterCircle) ∉ c.joins →
        ContDiffAt ℝ ∞ (realLift W) t ∧
          0 < inner ℝ (W (t : ParameterCircle))
            (o.rightAngleRotation (deriv (realLift c.parametrization) t))) →
      ∀ (n : ℕ) (p : Polygon Plane n), PolygonTurning.IsSimple p →
      ∀ f : C(ParameterCircle, ℝ),
        (∀ q, |f q| < a / 4) →
        p.boundary ℝ = range (fun q => e (q, f q)) →
        (∀ (i : Fin n) (t : ℝ), t ∈ Ioo (0 : ℝ) 1 →
          0 < inner ℝ (W ((e.symm (p.edgePath ℝ i t)).1))
            (o.rightAngleRotation (PolygonTurning.edgeVector p i))) →
        ∃ UQ : Set Plane, PolygonTurning.IsBoundedSide p UQ ∧
          PolygonTurning.HasBoundedSideOnLeft o p UQ

end Expected
end P202Specs.TransversePolygonGraphTransport
