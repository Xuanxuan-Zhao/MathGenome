import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GlobalGaussBonnetLocalization

/-!
Independent boundary-gluing obligation for paper.tex 5107–5117 and 5130–5135.
All geometric objects and both literal integrals are the canonical upstream
objects. In particular a regional chart carries genuine metric-preserving
immersions and its actual Levi–Civita connection, not a cancellation certificate.
The statement quantifies over every decomposition and every presentation.
-/
set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData
open P202.MetricData P202.ConnectionData
open P202Specs.GlobalGaussBonnet P202Specs.SurfaceRegionConstruction
open P202Specs.PlanarRegionTopology

namespace P202Specs.GlobalGaussBonnet.BoundaryGluingExpected
universe u

/-- All interior edge terms cancel and the remaining terms are exactly the
original inward-normal boundary integral, for any genuine boundary presentation.
There is no orientation, connectedness or nonemptiness hypothesis on the surface.
No incidence, normal comparison or integral-transport premise is supplied. -/
def regional_boundary_gluing : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} [CompactSpace M]
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)),
    P202.LeviCivitaData.IsLeviCivita g C →
    ∀ (D : RegionDecomposition S)
      (G : ∀ j : Fin D.regionCount, RegionalChartGeometry g D j)
      (A : ∀ (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount),
        P202Specs.PlaneTurning.ArcPresentation ((D.region j).curve i))
      (s : ∀ j : Fin D.regionCount, Fin (D.region j).boundaryCount → ℝ),
      (∀ j, IsInducedBoundaryOrientation (D.region j) (s j)) →
      ∀ B : BoundaryPresentation g,
        (∑ j : Fin D.regionCount,
          P202Specs.LocalGaussBonnet.geodesicIntegral
            (G j).metric (G j).connection (G j).orientation
            (G j).ambientChart (G j).ambientChart_mem (D.region j) (A j) (s j)) =
          B.curvatureIntegral C

end P202Specs.GlobalGaussBonnet.BoundaryGluingExpected
