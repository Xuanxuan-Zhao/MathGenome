import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.LocalGaussBonnet
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SurfaceRegionsEuler

/-!
Canonical geometry and analytic localization for paper.tex 5093–5137. Area is measured by the measure
representing the canonical metric-density integral, rather than an oriented
volume form. The boundary integral is an unsigned arc-length integral paired
with the actual inward normal. The finite presentation is constructed in the
conclusion, and the identity is required for every such presentation.

Neither connectedness, nonemptiness nor an orientation is an input. The two
model kinds retain both closed surfaces and surfaces with smooth boundary.
No regional Gauss–Bonnet, cancellation, angle-sum, or null-area certificate
is included among the hypotheses.
-/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators CompactlySupported
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData

namespace P202Specs.GlobalGaussBonnet
open P202.MetricData P202.ConnectionData P202.CurvatureData
  P202.SurfaceBoundaryData
universe u
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}

/-- The sectional curvature of the actual tangent plane. This is the same
Gram quotient as in LocalGaussBonnet, extended to either model kind. -/
def gaussianCurvature (g : RiemannianMetric S) (T : CurvatureTensor S) (p : M) : ℝ :=
  let b := referenceBasis g p
  curvatureForm g T p (b 0) (b 1) (b 1) (b 0) /
    (pairing g p (b 0) (b 0) * pairing g p (b 1) (b 1) -
      pairing g p (b 0) (b 1) ^ 2)

/-- Intrinsic characterization of the canonical Riemannian area measure.
Existence is part of the conclusion below, and is supplied upstream by
RiemannianVolume. The measurable space is the Borel space of the given topology. -/
def IsAreaMeasure (g : RiemannianMetric S) : @Measure M (borel M) → Prop :=
  letI : MeasurableSpace M := borel M
  fun μ => μ.Regular ∧
    (∀ A : Set M, IsCompact A → μ A < ⊤) ∧
    ∀ f : C_c(M, ℝ), (∫ p, f p ∂μ) = P202.VolumeData.integral g f

def totalCurvature (g : RiemannianMetric S) (T : CurvatureTensor S)
    (μ : @Measure M (borel M)) : ℝ :=
  letI : MeasurableSpace M := borel M
  ∫ p, gaussianCurvature g T p ∂μ

/-- A finite, multiplicity-one presentation of the genuine intrinsic boundary.
Each open arc is embedded and different open arcs are disjoint. Endpoint
values have zero arc-length mass. `side` describes S itself locally by a
regular defining function nonnegative on its inward side; it supplies no
curvature or integration identity. -/
structure BoundaryPresentation (g : RiemannianMetric S) where
  count : ℕ
  arc : Fin count → RegularArc g
  injective : ∀ i, Set.InjOn (arc i).curve (Ioo (arc i).left (arc i).right)
  disjoint : Pairwise (fun i j => Disjoint
    ((arc i).curve '' Ioo (arc i).left (arc i).right)
    ((arc j).curve '' Ioo (arc j).left (arc j).right))
  covers : SmoothManifolds.BoundaryData.intrinsicBoundary S =
    ⋃ i, (arc i).curve '' Icc (arc i).left (arc i).right
  side : ∀ i t, t ∈ Ioo (arc i).left (arc i).right →
    BoundarySideAt (S := S) univ ((arc i).curve t)

/-- The actual inward geodesic curvature times metric speed. The values at
arc endpoints and outside the parameter interval are set to zero. -/
def BoundaryPresentation.curvatureIntegrand {g : RiemannianMetric S}
    (B : BoundaryPresentation g) (C : Connection (tangentBundle S))
    (i : Fin B.count) (t : ℝ) : ℝ :=
  if ht : t ∈ Ioo (B.arc i).left (B.arc i).right then
    inwardCurvature g ((B.arc i).curve t)
      (curvatureVector C g (B.arc i).curve (B.arc i).tangent (B.arc i).speed t)
      (boundaryNormal g (B.side i t ht)) * (B.arc i).speed t
  else 0

def BoundaryPresentation.curvatureIntegral {g : RiemannianMetric S}
    (B : BoundaryPresentation g) (C : Connection (tangentBundle S)) : ℝ :=
  ∑ i, ∫ t in (B.arc i).left..(B.arc i).right, B.curvatureIntegrand C i t

open SmoothManifolds.ModelData SmoothManifolds.BundleOperationsData
open SmoothManifolds.OrientationData
open P202Specs.SurfaceRegionConstruction P202Specs.SurfaceRegionsEuler

/-- Genuine oriented ambient Riemannian geometry for one original component
closure. No regional area, curvature, turning, boundary gluing or angle sum
identity is included in these data. -/
structure RegionalChartGeometry {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount) where
  neighborhood : Set M
  neighborhood_open : IsOpen neighborhood
  closure_subset : regionClosure D r ⊆ neighborhood
  source_subset : neighborhood ⊆ (D.chart r).source
  restriction : SmoothManifold 2 a neighborhood
  inclusion : SmoothImmersion restriction S Subtype.val
  restrictedChart : ModelChart 2 a neighborhood
  restrictedChart_mem : restrictedChart ∈ restriction.smoothStructure.val
  restrictedChart_source : restrictedChart.source = univ
  restrictedChart_eq : ∀ p : neighborhood, restrictedChart p = D.chart r p.val
  ambientDomain : Set (Euclidean 2)
  ambientDomain_open : IsOpen ambientDomain
  ambientSurface : SmoothManifold 2 .euclidean (ULift.{u} ambientDomain)
  metric : RiemannianMetric ambientSurface
  connection : Connection (tangentBundle ambientSurface)
  connection_LC : P202.LeviCivitaData.IsLeviCivita metric connection
  curvature : CurvatureTensor ambientSurface
  curvature_represents : RepresentsCurvature connection curvature
  ambientChart : ModelChart 2 .euclidean (ULift.{u} ambientDomain)
  ambientChart_mem : ambientChart ∈ ambientSurface.smoothStructure.val
  ambientChart_source : ambientChart.source = univ
  map : neighborhood → ULift.{u} ambientDomain
  immersion : SmoothImmersion restriction ambientSurface map
  matching_coordinates : ∀ p : neighborhood,
    (restrictedChart p).val = (ambientChart (map p)).val
  metric_preserving : ∀ p v w,
    pairing metric (map p) (immersion.differential p v) (immersion.differential p w) =
      pairing g p.val (inclusion.differential p v) (inclusion.differential p w)
  orientation : Orientation ambientSurface
  orientation_positive : P202Specs.ChartRegionStokes.PositiveChart
    (P202.VolumeData.cotangentBundle ambientSurface) orientation ambientChart ambientChart_mem


namespace LocalizationExpected
open P202Specs.PlanarRegionTopology

/-- Independent full proposition for `exists_boundaryPresentation`. -/
def exists_boundaryPresentation : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} [CompactSpace M]
    (g : RiemannianMetric S),
    Nonempty (BoundaryPresentation g)

/-- Independent full proposition for `exists_unique_areaMeasure`. -/
def exists_unique_areaMeasure : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S),
    ∃! μ : @Measure M (borel M), IsAreaMeasure g μ

/-- Independent full proposition for `continuous_gaussianCurvature`. -/
def continuous_gaussianCurvature : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T),
    Continuous (gaussianCurvature g T)

/-- Independent full proposition for `integrableOn_gaussianCurvature_of_isCompact`. -/
def integrableOn_gaussianCurvature_of_isCompact : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ)
    (A : Set M) (hA : IsCompact A) (hAm : @MeasurableSet M (borel M) A),
    letI : MeasurableSpace M := borel M
    MeasureTheory.IntegrableOn (gaussianCurvature g T) A μ

/-- Independent full proposition for `integrable_gaussianCurvature`. -/
def integrable_gaussianCurvature : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} [CompactSpace M]
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ),
    letI : MeasurableSpace M := borel M
    MeasureTheory.Integrable (gaussianCurvature g T) μ

/-- Independent full proposition for `boundary_curvatureIntegrand_integrable`. -/
def boundary_curvatureIntegrand_integrable : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (B : BoundaryPresentation g) (i : Fin B.count),
    IntervalIntegrable (B.curvatureIntegrand C i) MeasureTheory.volume
      (B.arc i).left (B.arc i).right

/-- Independent full proposition for `boundary_curvatureIntegral_eq`. -/
def boundary_curvatureIntegral_eq : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {g : RiemannianMetric S}
    (B D : BoundaryPresentation g) (C : Connection (tangentBundle S)),
    B.curvatureIntegral C = D.curvatureIntegral C

/-- Independent full proposition for `exists_regionalChartGeometry`. -/
def exists_regionalChartGeometry : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount),
    Nonempty (RegionalChartGeometry g D r)

/-- Independent full proposition for `regionalChartGeometry_carrier_subset`. -/
def regionalChartGeometry_carrier_subset : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} {g : RiemannianMetric S}
    {D : RegionDecomposition S} {r : Fin D.regionCount}
    (G : RegionalChartGeometry g D r),
    (D.region r).carrier ⊆ P202Specs.ChartRegionStokes.chartTarget G.ambientChart

/-- Independent full proposition for `regionalChartGeometry_gaussianCurvature`. -/
def regionalChartGeometry_gaussianCurvature : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} {g : RiemannianMetric S}
    {D : RegionDecomposition S} {r : Fin D.regionCount}
    (G : RegionalChartGeometry g D r)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (p : G.neighborhood),
    gaussianCurvature g T p.val = gaussianCurvature G.metric G.curvature (G.map p)

/-- Independent full proposition for `regionalChartGeometry_curvatureIntegral`. -/
def regionalChartGeometry_curvatureIntegral : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} {g : RiemannianMetric S}
    {D : RegionDecomposition S} {r : Fin D.regionCount}
    (G : RegionalChartGeometry g D r)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ),
    (letI : MeasurableSpace M := borel M;
      ∫ p in regionClosure D r, gaussianCurvature g T p ∂μ) =
      P202Specs.LocalGaussBonnet.curvatureIntegral G.metric G.curvature
        G.ambientChart G.ambientChart_mem (D.region r)

/-- Independent full proposition for `region_integrableOn_gaussianCurvature`. -/
def region_integrableOn_gaussianCurvature : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ)
    (D : RegionDecomposition S) (r : Fin D.regionCount),
    letI : MeasurableSpace M := borel M
    IntegrableOn (gaussianCurvature g T) (regionClosure D r) μ

/-- Independent full proposition for `regionalChartGeometry_local_formula`. -/
def regionalChartGeometry_local_formula : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} {g : RiemannianMetric S}
    {D : RegionDecomposition S} {r : Fin D.regionCount}
    (G : RegionalChartGeometry g D r)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ),
    (∃ s, IsInducedBoundaryOrientation (D.region r) s) ∧
      Nonempty (∀ b, P202Specs.PlaneTurning.ArcPresentation ((D.region r).curve b)) ∧
      ∀ (A : ∀ b, P202Specs.PlaneTurning.ArcPresentation ((D.region r).curve b))
        (s : Fin (D.region r).boundaryCount → ℝ),
        IsInducedBoundaryOrientation (D.region r) s →
        IntegrableOn (P202Specs.LocalGaussBonnet.curvatureIntegrand G.metric G.curvature
          G.ambientChart G.ambientChart_mem) (D.region r).carrier ∧
        (∀ b k, IntervalIntegrable
          (P202Specs.LocalGaussBonnet.geodesicIntegrand G.metric G.connection G.orientation
            G.ambientChart G.ambientChart_mem (A b) k) volume 0 1) ∧
        (∀ b k, 0 < P202Specs.LocalGaussBonnet.interiorAngle G.metric G.orientation
            G.ambientChart G.ambientChart_mem (A b) (s b) k ∧
          P202Specs.LocalGaussBonnet.interiorAngle G.metric G.orientation
            G.ambientChart G.ambientChart_mem (A b) (s b) k < 2 * Real.pi) ∧
        (∀ b k, P202Specs.MetricBoundaryTurning.IsOccupiedSectorAngle
          G.metric G.orientation G.ambientChart G.ambientChart_mem (D.region r) b (A b) (s b) k
          (P202Specs.LocalGaussBonnet.interiorAngle G.metric G.orientation
            G.ambientChart G.ambientChart_mem (A b) (s b) k)) ∧
        ∃ hD : P202Specs.EulerPoincare.HomologyFiniteType ℚ (D.region r).carrier,
          (letI : MeasurableSpace M := borel M;
            ∫ p in regionClosure D r, gaussianCurvature g T p ∂μ) +
            P202Specs.LocalGaussBonnet.geodesicIntegral G.metric G.connection G.orientation
              G.ambientChart G.ambientChart_mem (D.region r) A s +
            P202Specs.LocalGaussBonnet.exteriorAngleSum G.metric G.orientation
              G.ambientChart G.ambientChart_mem (D.region r) A s =
              2 * Real.pi * (P202Specs.EulerPoincare.topologicalEuler (D.region r).carrier hD : ℝ)

/-- Independent full proposition for `regionDecomposition_graph_area_null`. -/
def regionDecomposition_graph_area_null : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S) (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ)
    (R : RegionDecomposition S),
    μ R.graph.carrier = 0

/-- Independent full proposition for `regionDecomposition_totalCurvature`. -/
def regionDecomposition_totalCurvature : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} [CompactSpace M]
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T)
    (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ)
    (R : P202Specs.SurfaceRegionConstruction.RegionDecomposition S),
    totalCurvature g T μ =
      (letI : MeasurableSpace M := borel M
       ∑ j, ∫ p in P202Specs.SurfaceRegionsEuler.regionClosure R j,
         gaussianCurvature g T p ∂μ)

/-- Independent full proposition for `regionDecomposition_integral`. -/
def regionDecomposition_integral : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S) (μ : @Measure M (borel M)) (hμ : IsAreaMeasure g μ)
    (R : RegionDecomposition S) (f : M → ℝ)
    (hf : letI : MeasurableSpace M := borel M
      ∀ j, IntegrableOn f (regionClosure R j) μ),
    letI : MeasurableSpace M := borel M
    Integrable f μ ∧ (∫ p, f p ∂μ) = ∑ j, ∫ p in regionClosure R j, f p ∂μ

/-- Independent full proposition for `exists_global_integrals`. -/
def exists_global_integrals : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (T : CurvatureTensor S) (hT : RepresentsCurvature C T),
    Nonempty (BoundaryPresentation g) ∧
      ∃ μ : @Measure M (borel M), IsAreaMeasure g μ ∧
        (letI : MeasurableSpace M := borel M; Integrable (gaussianCurvature g T) μ) ∧
        ∀ B : BoundaryPresentation g, ∀ i,
          IntervalIntegrable (B.curvatureIntegrand C i) volume
            (B.arc i).left (B.arc i).right

end LocalizationExpected
end P202Specs.GlobalGaussBonnet
