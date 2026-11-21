import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.MetricFoundation

/-! The local upper length estimate, for the intrinsic metric and the actual
compact-interval piecewise C¹ curves, including both model kinds and rank zero. -/
set_option autoImplicit false
namespace P202Specs.Geometry.LocalShortCurves
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
open P202.MetricData P202.CurveData
universe u

def local_short_curvesType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n kind M) (g : RiemannianMetric S)
    (p : M) (ε : ℝ), 0 < ε →
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∀ q ∈ U,
      ∃ a b : ℝ, ∃ c : PiecewiseC1Curve S a b,
        c a = p ∧ c b = q ∧ length g c < ε

end P202Specs.Geometry.LocalShortCurves
