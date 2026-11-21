import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GlobalGaussBonnetLocalization

/-!
Independent local corner ledger for paper.tex 5117–5133. The index sets are
those of every actual regional presentation. Original points are tested in
the assigned chart source, since a chart has arbitrary values off its source.
Neither sector/corner correspondences nor angle identities are hypotheses.
-/
set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
open P202.MetricData
open P202Specs.PlanarRegionTopology P202Specs.PlaneTurning
open P202Specs.SurfaceRegionConstruction P202Specs.SurfaceRegionsEuler
open P202Specs.GlobalGaussBonnet

namespace P202Specs.RegionalVertexCorners
universe u
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- Both labelled endpoint pairs of a loop are retained. -/
def vertexDegree (G : EmbeddedGraph S) (v : Fin G.vertexCount) : ℕ :=
  ∑ h : Fin G.edgeCount × Bool,
    if (if h.2 then G.terminal h.1 else G.initial h.1) = v then 1 else 0

/-- A literal presentation join at an actual original point. -/
def CornerAt (D : RegionDecomposition S) (r : Fin D.regionCount)
    (i : Fin (D.region r).boundaryCount)
    (A : ArcPresentation ((D.region r).curve i)) (k : Fin A.count) (p : M) : Prop :=
  p ∈ (D.chart r).source ∧ coordinates (D.chart r) p = A.arc k 1

/-- The literal exterior-angle summand of the upstream local theorem. -/
def cornerTerm (g : RiemannianMetric S) (D : RegionDecomposition S)
    (r : Fin D.regionCount) (G : RegionalChartGeometry g D r)
    (i : Fin (D.region r).boundaryCount)
    (A : ArcPresentation ((D.region r).curve i)) (s : ℝ) (k : Fin A.count) : ℝ :=
  Real.pi - P202Specs.LocalGaussBonnet.interiorAngle
    G.metric G.orientation G.ambientChart G.ambientChart_mem A s k

/-- Sum over all actual presentation corners at p, with no assigned incidence
certificate and no requirement that a presentation lists all graph vertices. -/
def cornerSumAt (g : RiemannianMetric S) (D : RegionDecomposition S)
    (G : ∀ r, RegionalChartGeometry g D r)
    (A : ∀ r i, ArcPresentation ((D.region r).curve i))
    (s : ∀ r, Fin (D.region r).boundaryCount → ℝ) (p : M) : ℝ := by
  classical
  exact ∑ r, ∑ i, ∑ k,
    if CornerAt D r i (A r i) k p then cornerTerm g D r (G r) i (A r i) (s r i) k else 0

namespace Expected
/-- Existence and uniqueness of the original point are derived from D. -/
def originalPoint : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (D : RegionDecomposition S)
    (r : Fin D.regionCount) (i : Fin (D.region r).boundaryCount)
    (A : ArcPresentation ((D.region r).curve i)) (k : Fin A.count),
    ∃! p : M, p ∈ regionClosure D r ∩ D.graph.carrier ∧ CornerAt D r i A k p

/-- Full local identity at every actual vertex of every decomposition. -/
def vertexCornerIdentity : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S) (D : RegionDecomposition S)
    (G : ∀ r, RegionalChartGeometry g D r)
    (A : ∀ r i, ArcPresentation ((D.region r).curve i))
    (s : ∀ r, Fin (D.region r).boundaryCount → ℝ),
    (∀ r, IsInducedBoundaryOrientation (D.region r) (s r)) →
    ∀ v : Fin D.graph.vertexCount,
      cornerSumAt g D G A s (D.graph.vertex v) =
        Real.pi * ((vertexDegree D.graph v : ℝ) - 2)

/-- Support: every actual presentation corner off the vertex set has zero
literal exterior contribution, including arbitrary smooth subdivisions. -/
def offVertexContribution_zero : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S) (D : RegionDecomposition S)
    (G : ∀ r, RegionalChartGeometry g D r)
    (A : ∀ r i, ArcPresentation ((D.region r).curve i))
    (s : ∀ r, Fin (D.region r).boundaryCount → ℝ),
    (∀ r, IsInducedBoundaryOrientation (D.region r) (s r)) →
    ∀ (r : Fin D.regionCount) (i : Fin (D.region r).boundaryCount)
      (k : Fin (A r i).count) (p : M),
      CornerAt D r i (A r i) k p → p ∉ range D.graph.vertex →
        cornerTerm g D r (G r) i (A r i) (s r i) k = 0
end Expected
end P202Specs.RegionalVertexCorners
