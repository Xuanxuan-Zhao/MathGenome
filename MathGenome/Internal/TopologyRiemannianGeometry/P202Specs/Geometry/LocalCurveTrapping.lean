import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PiecewiseCurves

/-! The raw local no-escape estimate, for the shared intrinsic metric and
compact-interval piecewise C¹ curves. No distance construction is assumed. -/
set_option autoImplicit false

namespace P202Specs.Geometry.LocalCurveTrapping
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData P202.MetricData P202.CurveData
universe u

def local_curve_trappingType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    (p : M) (U : Set M), IsOpen U → p ∈ U →
    ∃ ε : ℝ, 0 < ε ∧ ∀ (a b : ℝ) (c : PiecewiseC1Curve S a b),
      c a = p → length g c < ε → c b ∈ U

end P202Specs.Geometry.LocalCurveTrapping
