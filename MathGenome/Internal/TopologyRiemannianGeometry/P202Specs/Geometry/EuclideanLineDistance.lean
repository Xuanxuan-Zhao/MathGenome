import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CompleteExponentialMinimizers
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.MetricGeodesicCompleteness

/-! The distance and completeness parts of the Euclidean-line counterexample
in paper.tex:4739–4742. The hypotheses specify the standard global coordinate
and the exact metric on the original intrinsic tangent fibers. -/
set_option autoImplicit false

namespace P202Specs.Geometry.EuclideanLineDistance
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.ConnectionData P202.CompleteExponentialData
  P202.CompletenessData Set

def euclidean_line_distanceType : Prop :=
  ∀ (S : SmoothManifold 1 .euclidean ℝ) (g : RiemannianMetric S),
    (∃ c ∈ S.smoothStructure.val, c.source = univ ∧ c.target = univ ∧
      ∀ x : ℝ, (c x).val 0 = x) →
    (∀ (x : ℝ) (v w : TangentSpace S x), pairing g x v w =
      scalarDerivative S (fun y : ℝ => y) x v *
        scalarDerivative S (fun y : ℝ => y) x w) →
    (∀ x y : ℝ, lengthDistance g x y = |x - y|) ∧
      LengthMetricComplete g ∧
      (∀ A : ℝ, 0 < A → ∃ x y : ℝ, A < lengthDistance g x y)

end P202Specs.Geometry.EuclideanLineDistance
