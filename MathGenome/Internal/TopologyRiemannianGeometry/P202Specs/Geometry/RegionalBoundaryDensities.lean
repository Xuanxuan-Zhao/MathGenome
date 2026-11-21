import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GlobalGaussBonnetLocalization

/-! Independent statements for paper.tex 4747–4757 and 5107–5117.
All objects are the upstream canonical ones. No normal, curvature or transport
identity is part of an arc representation. No global integral sum is asserted.
-/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology Classical
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.MetricData P202.ConnectionData P202.SurfaceBoundaryData
open P202Specs.GlobalGaussBonnet P202Specs.SurfaceRegionConstruction
open P202Specs.SurfaceRegionsEuler P202Specs.PlanarRegionTopology

namespace P202Specs.RegionalBoundaryDensities
universe u
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- Only literal coordinates on the full compact parameter interval. -/
def RepresentsRegionalArc {g : RiemannianMetric S} (D : RegionDecomposition S)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount)
    (A : PlaneTurning.ArcPresentation ((D.region j).curve i)) (k : Fin A.count)
    (c : RegularArc g) : Prop :=
  c.left = 0 ∧ c.right = 1 ∧ ∀ t ∈ Icc (0 : ℝ) 1,
    c.curve t ∈ (D.chart j).source ∧ coordinates (D.chart j) (c.curve t) = A.arc k t

/-- The exceptions use only original Jordan joins and graph vertices.
Presentation endpoints are excluded by the open parameter interval. -/
def exceptionalParameters (D : RegionDecomposition S)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount)
    (A : PlaneTurning.ArcPresentation ((D.region j).curve i)) (k : Fin A.count) : Set ℝ :=
  Ioo (0 : ℝ) 1 ∩
    ({t | ((A.time k.castSucc + (A.time k.succ - A.time k.castSucc) * t : ℝ) :
      ParameterCircle) ∈ ((D.region j).curve i).joins} ∪
    (A.arc k ⁻¹' (coordinates (D.chart j) '' range D.graph.vertex)))

namespace Expected

def exceptionalParameters_finite : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (D : RegionDecomposition S)
    (j : Fin D.regionCount) (i : Fin (D.region j).boundaryCount)
    (A : PlaneTurning.ArcPresentation ((D.region j).curve i)) (k : Fin A.count),
    (exceptionalParameters D j i A k).Finite

def regionalSide_exists : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (j : Fin D.regionCount)
    (s : Fin (D.region j).boundaryCount → ℝ),
    IsInducedBoundaryOrientation (D.region j) s →
    ∀ (i : Fin (D.region j).boundaryCount)
      (A : PlaneTurning.ArcPresentation ((D.region j).curve i)) (k : Fin A.count)
      (c : RegularArc g), RepresentsRegionalArc D j i A k c →
    ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ exceptionalParameters D j i A k →
      Nonempty (BoundarySideAt (S := S) (regionClosure D j) (c.curve t))

/-- The principal density statement, for EVERY original G, A, sign, and ANY
literal genuine original-surface representation; EVERY genuine side is allowed.
Both model kinds and arbitrary universes are retained. -/
def regional_density_eq : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), P202.LeviCivitaData.IsLeviCivita g C →
    ∀ (D : RegionDecomposition S) (j : Fin D.regionCount)
      (G : RegionalChartGeometry g D j) (s : Fin (D.region j).boundaryCount → ℝ),
    IsInducedBoundaryOrientation (D.region j) s →
    ∀ (i : Fin (D.region j).boundaryCount)
      (A : PlaneTurning.ArcPresentation ((D.region j).curve i)) (k : Fin A.count)
      (c : RegularArc g), RepresentsRegionalArc D j i A k c →
    ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ exceptionalParameters D j i A k →
    ∀ b : BoundarySideAt (S := S) (regionClosure D j) (c.curve t),
      s i * LocalGaussBonnet.geodesicIntegrand G.metric G.connection G.orientation
        G.ambientChart G.ambientChart_mem A k t =
      inwardCurvature g (c.curve t)
        (curvatureVector C g c.curve c.tangent c.speed t) (boundaryNormal g b) * c.speed t

/-- Actual occupied sets with disjoint interiors have opposite normals at
an original interior point, for either original model kind. -/
def boundaryNormals_opposite : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    {D E : Set M} {p : M}, p ∉ SmoothManifolds.BoundaryData.intrinsicBoundary S →
    ∀ (b : BoundarySideAt (S := S) D p) (a : BoundarySideAt (S := S) E p),
      Disjoint (interior D) (interior E) → boundaryNormal g a = -boundaryNormal g b

/-- This stronger form permits any genuine presentation's surface side. -/
def boundaryNormal_eq_surfaceNormal : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S) {D : Set M} {p : M},
    p ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S →
    ∀ (b : BoundarySideAt (S := S) D p) (bS : BoundarySideAt (S := S) univ p),
      D ∈ 𝓝 p → boundaryNormal g b = boundaryNormal g bS

/-- Either increasing or decreasing genuine transitions are covered. The
connection is arbitrary, so in particular this holds for the actual LC one. -/
def regularArc_curvatureVector_reparam : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {g : RiemannianMetric S}
    (C : Connection (tangentBundle S)) (c d : RegularArc g)
    (φ : ℝ → ℝ) {l r s : ℝ}, s ∈ Ioo l r →
    Ioo l r ⊆ Ioo c.left c.right → MapsTo φ (Ioo l r) (Ioo d.left d.right) →
    InjOn φ (Ioo l r) → (∀ x ∈ Ioo l r, HasDerivAt φ (deriv φ x) x) →
    (∀ x ∈ Ioo l r, d.curve (φ x) = c.curve x) →
    HEq (curvatureVector C g c.curve c.tangent c.speed s)
      (curvatureVector C g d.curve d.tangent d.speed (φ s))

def regularArc_speed_transition : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {g : RiemannianMetric S}
    (c d : RegularArc g) (φ : ℝ → ℝ) (s a : ℝ),
    s ∈ Ioo c.left c.right → φ s ∈ Ioo d.left d.right → HasDerivAt φ a s →
    (d.curve ∘ φ) =ᶠ[𝓝 s] c.curve → c.speed s = |a| * d.speed (φ s)

/-- Density transport on the same actual occupied set, for every genuine
choice of its defining function; both transition directions are included. -/
def regularArc_inwardDensity_reparam : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {g : RiemannianMetric S}
    (C : Connection (tangentBundle S)) (c d : RegularArc g)
    (φ : ℝ → ℝ) {l r s : ℝ}, s ∈ Ioo l r →
    Ioo l r ⊆ Ioo c.left c.right → MapsTo φ (Ioo l r) (Ioo d.left d.right) →
    InjOn φ (Ioo l r) → (∀ x ∈ Ioo l r, HasDerivAt φ (deriv φ x) x) →
    (∀ x ∈ Ioo l r, d.curve (φ x) = c.curve x) →
    ∀ {D : Set M} (b : BoundarySideAt (S := S) D (c.curve s))
      (a : BoundarySideAt (S := S) D (d.curve (φ s))),
    inwardCurvature g (c.curve s)
      (curvatureVector C g c.curve c.tangent c.speed s) (boundaryNormal g b) * c.speed s =
    inwardCurvature g (d.curve (φ s))
      (curvatureVector C g d.curve d.tangent d.speed (φ s)) (boundaryNormal g a) *
        d.speed (φ s) * |deriv φ s|

end Expected
end P202Specs.RegionalBoundaryDensities
