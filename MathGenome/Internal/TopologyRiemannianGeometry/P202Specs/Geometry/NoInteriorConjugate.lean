import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.MinimizingIndexForm
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ExponentialJacobi

/-! Independent statement of `cor:p202-no-interior-conjugate`, paper.tex
4145–4179. Closed-segment equations use within derivatives so that the
values of total representatives outside the segment impose no regularity
assumptions. In particular constant minimizing segments are included. -/
set_option autoImplicit false
namespace P202.NoInteriorConjugateData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.ConnectionData P202.CurveConnectionData
  P202.FirstVariationData P202.SecondVariationData P202.CurvatureData
open Set
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- The intrinsic Jacobi equation on a closed segment, including both
one-sided endpoint equations. This is an equation, not a solution certificate
or a positivity assumption. -/
def IsSegmentJacobiField (C : Connection (tangentBundle S))
    (R : CurvatureTensor S) (γ : ℝ → M) (a c : ℝ)
    (J : (t : ℝ) → TangentSpace S (γ t)) : Prop :=
  ∃ D : (t : ℝ) → TangentSpace S (γ t), ∀ t ∈ Icc a c,
    HasCovariantDerivativeWithinAt C γ J (Icc a c) t (D t) ∧
    HasCovariantDerivativeWithinAt C γ D (Icc a c) t
      (-(R.val (γ t) (J t) (segmentTangent S γ a c t)
        (segmentTangent S γ a c t)))

/-- Conjugacy is along this specified segment. Nonzeroness is tested on
its parameter domain, not on the arbitrary ambient representative. -/
def SegmentConjugate (C : Connection (tangentBundle S))
    (R : CurvatureTensor S) (γ : ℝ → M) (a c : ℝ) : Prop :=
  ∃ J : (t : ℝ) → TangentSpace S (γ t),
    IsSegmentJacobiField C R γ a c J ∧ J a = 0 ∧ J c = 0 ∧
      ∃ t ∈ Icc a c, J t ≠ 0

end P202.NoInteriorConjugateData

namespace P202Specs.Geometry.NoInteriorConjugate
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.CurveData P202.ConnectionData P202.LeviCivitaData
  P202.CurvatureData P202.SecondVariationData P202.MinimizingIndexData
  P202.NoInteriorConjugateData
universe u

/-- Only strictly interior times are excluded. There is no completeness,
positive speed, positive dimension, or nonconstancy hypothesis. -/
def no_interior_conjugateType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ {a b : ℝ} (γ : PiecewiseC1Curve S a b), a < b →
      IsAffineGeodesicSegment C γ a b → IsLengthMinimizing g γ →
      ∀ c : ℝ, a < c → c < b → ¬ SegmentConjugate C R γ a c

end P202Specs.Geometry.NoInteriorConjugate
