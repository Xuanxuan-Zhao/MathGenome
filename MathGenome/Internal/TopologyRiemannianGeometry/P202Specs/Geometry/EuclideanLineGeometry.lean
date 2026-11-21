import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.MyersDiameterCompact

/-! The standard real line and its intrinsic dx² metric, for the n=1
counterexample following Bonnet–Myers (paper.tex:4739–4742). -/
set_option autoImplicit false
namespace P202Specs.Geometry.EuclideanLineGeometry
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData
  P202.CurvatureData P202.RicciData P202.MyersData
open Set

/-- Existence includes the standard global chart, the precise metric formula,
and genuine Levi-Civita and curvature representatives. -/
def euclidean_line_geometryType : Prop :=
  ∃ (S : SmoothManifold 1 .euclidean ℝ) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S),
    (∃ c ∈ S.smoothStructure.val,
      c.source = univ ∧ c.target = univ ∧ ∀ x : ℝ, (c x).val 0 = x) ∧
    (∀ (x : ℝ) (v w : TangentSpace S x), pairing g x v w =
      scalarDerivative S (fun y : ℝ => y) x v *
      scalarDerivative S (fun y : ℝ => y) x w) ∧
    IsLeviCivita g C ∧ RepresentsCurvature C R ∧
    (∀ x : ℝ, ricci R x = 0) ∧
    ∀ k : ℝ, 0 < k → RicciLowerBound g R k

end P202Specs.Geometry.EuclideanLineGeometry
