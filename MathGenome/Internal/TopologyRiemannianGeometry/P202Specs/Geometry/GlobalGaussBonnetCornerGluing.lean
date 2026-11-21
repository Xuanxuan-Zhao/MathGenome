import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GlobalGaussBonnetLocalization

/-!
Independent full corner-gluing proposition for paper.tex 5117–5128.
The geometric packages, boundary presentations, and induced signs are arbitrary.
The sum is the literal ambient metric exterior-angle sum, without any assumed
sector correspondence, angle identity, or restriction on graph-star valence.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData
open P202.MetricData
open P202Specs.SurfaceRegionConstruction P202Specs.GlobalGaussBonnet

namespace P202Specs.GlobalGaussBonnet.CornerGluingExpected
universe u

/-- The actual regional exterior angles count both half-edges of every edge,
including loops, on every original compact surface of either model kind. -/
def regionalExteriorAngleSum : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} [CompactSpace M]
    (g : RiemannianMetric S) (D : RegionDecomposition S)
    (G : ∀ j, RegionalChartGeometry g D j)
    (A : ∀ j i, P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
    (s : ∀ j, Fin (D.region j).boundaryCount → ℝ),
    (∀ j, P202Specs.PlanarRegionTopology.IsInducedBoundaryOrientation (D.region j) (s j)) →
    (∑ j, P202Specs.LocalGaussBonnet.exteriorAngleSum
      (G j).metric (G j).orientation (G j).ambientChart (G j).ambientChart_mem
      (D.region j) (A j) (s j)) =
      2 * Real.pi * ((D.graph.edgeCount : ℝ) - (D.graph.vertexCount : ℝ))

end P202Specs.GlobalGaussBonnet.CornerGluingExpected
