import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlaneTurning
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ChartRegionStokes
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SurfaceBoundaryGeometry
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CurvatureAlgebra
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlanarRegionEuler
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.MetricBoundaryTurning

/-!
Independent target for paper.tex 4919–4994. The surface, metric, connection,
curvature tensor, chart, region and parametrized boundary are the shared
objects. No connection-form, turning, Stokes, or frame-change certificate is
part of the input. A finite smooth boundary presentation is constructed in
the conclusion; the identity then holds for every such presentation.

All area integrals are written in the given positive chart, with the actual
metric Gram density. Boundary integrals use the intrinsic covariant derivative
and unsigned metric speed. The sign of each boundary traversal is applied to
both geodesic curvature and exterior angles. Thus inner components and reflex
corners are included. The occupied-sector clause identifies these angles
with the actual domain, and a one-component region gives the disk formula.
-/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators Classical

namespace P202Specs.LocalGaussBonnet
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleOperationsData
open P202.MetricData P202.ConnectionData P202.CurvatureData
  P202.SurfaceBoundaryData
open P202Specs.PlanarRegionTopology

universe u
variable {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M}

/-- The sectional-curvature scalar in the shared reference basis. Its Gram
denominator is retained, so the definition does not presuppose an unproved
normalization or a curvature sign. Sectional basis independence identifies
this with K in every tangent two-plane. -/
def gaussianCurvature (g : RiemannianMetric S) (T : CurvatureTensor S) (p : M) : ℝ :=
  let b := referenceBasis g p
  curvatureForm g T p (b 0) (b 1) (b 1) (b 0) /
    (pairing g p (b 0) (b 0) * pairing g p (b 1) (b 1) -
      pairing g p (b 0) (b 1) ^ 2)

/-- The actual inverse coordinate map. -/
def chartPoint (c : ModelChart 2 .euclidean M) (x : Plane) : M :=
  c.symm (ChartRegionStokes.modelPoint x)

/-- Pullback of an ordinary coordinate vector to the original tangent fiber.
The zero fallback lies outside the chart target and is never used on D. -/
def chartVector (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (x v : Plane) : TangentSpace S (chartPoint c x) :=
  if hx : ChartRegionStokes.modelPoint x ∈ c.target then
    ((tangentStructure S).fiberCoordinates.equiv c hc (chartPoint c x)
      (c.map_target hx)).symm (EuclideanSpace.equiv (Fin 2) ℝ v)
  else 0

/-- Literal sqrt(det g) in this chart, using the canonical tangent realization. -/
def areaWeight (g : RiemannianMetric S) (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (x : Plane) : ℝ :=
  if hx : ChartRegionStokes.modelPoint x ∈ c.target then
    Real.sqrt (P202.VolumeData.gramMatrix g (tangentStructure S).fiberCoordinates c hc
      ⟨chartPoint c x, c.map_target hx⟩).det
  else 0

def curvatureIntegrand (g : RiemannianMetric S) (T : CurvatureTensor S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val) (x : Plane) : ℝ :=
  gaussianCurvature g T (chartPoint c x) * areaWeight g c hc x

def curvatureIntegral (g : RiemannianMetric S) (T : CurvatureTensor S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (R : PlanarRegion) : ℝ :=
  ∫ x in R.carrier, curvatureIntegrand g T c hc x

def surfaceArc {q : RegularJordanCurve} (c : ModelChart 2 .euclidean M)
    (A : PlaneTurning.ArcPresentation q) (j : Fin A.count) (t : ℝ) : M :=
  chartPoint c (A.arc j t)

def arcVelocity {q : RegularJordanCurve} (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (A : PlaneTurning.ArcPresentation q)
    (j : Fin A.count) (t : ℝ) : TangentSpace S (surfaceArc c A j t) :=
  chartVector c hc (A.arc j t) (PlaneTurning.velocity A j t)

def arcSpeed {q : RegularJordanCurve} (g : RiemannianMetric S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A : PlaneTurning.ArcPresentation q) (j : Fin A.count) (t : ℝ) : ℝ :=
  tangentNorm g (surfaceArc c A j t) (arcVelocity c hc A j t)

/-- k_g ds/dt, using T = velocity / |velocity| and D_T T = D_t T / speed. -/
def geodesicIntegrand {q : RegularJordanCurve}
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A : PlaneTurning.ArcPresentation q) (j : Fin A.count) (t : ℝ) : ℝ :=
  signedCurveCurvature C g o (surfaceArc c A j)
    (unitTangent g (surfaceArc c A j) (arcVelocity c hc A j))
    (arcSpeed g c hc A j) t * arcSpeed g c hc A j t

/-- The metric exterior angle of the actual one-sided velocities. Both
vectors live at the common endpoint, so no choice of fiber transport occurs. -/
def metricCornerAngle {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A : PlaneTurning.ArcPresentation q) (j : Fin A.count) : ℝ := by
  let p := chartPoint c (A.arc j 1)
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  exact ((planeOrientation g o p).oangle
    (chartVector c hc (A.arc j 1) (PlaneTurning.velocity A j 1))
    (chartVector c hc (A.arc j 1)
      (PlaneTurning.velocity A (finRotate A.count j) 0))).toReal

/-- The interior angle of the locally occupied side, encoded by the signed
short turn. Showing its geometric interpretation is a proof obligation. -/
def interiorAngle {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A : PlaneTurning.ArcPresentation q) (s : ℝ) (j : Fin A.count) : ℝ :=
  Real.pi - s * metricCornerAngle g o c hc A j

def geodesicIntegral (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (R : PlanarRegion) (A : ∀ i, PlaneTurning.ArcPresentation (R.curve i))
    (s : Fin R.boundaryCount → ℝ) : ℝ :=
  ∑ i, s i * ∑ j, ∫ t in (0 : ℝ)..1, geodesicIntegrand g C o c hc (A i) j t

def exteriorAngleSum (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (R : PlanarRegion) (A : ∀ i, PlaneTurning.ArcPresentation (R.curve i))
    (s : Fin R.boundaryCount → ℝ) : ℝ :=
  ∑ i, ∑ j, (Real.pi - interiorAngle g o c hc (A i) (s i) j)

namespace Expected

/-- Full original target, without any conditional-draft premises. In
particular, all smooth boundary decompositions must give the same formula.
The Euler invariant is the original rational singular-homology invariant. -/
def localGaussBonnet : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] (S : SmoothManifold 2 .euclidean M)
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)),
    P202.LeviCivitaData.IsLeviCivita g C →
    ∀ (T : CurvatureTensor S), RepresentsCurvature C T →
    ∀ (o : SmoothManifolds.OrientationData.Orientation S)
      (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val),
      ChartRegionStokes.PositiveChart (P202.VolumeData.cotangentBundle S) o c hc →
    ∀ R : PlanarRegion, R.carrier ⊆ ChartRegionStokes.chartTarget c →
      (Nonempty (∀ i, PlaneTurning.ArcPresentation (R.curve i))) ∧
      ∀ (A : ∀ i, PlaneTurning.ArcPresentation (R.curve i))
        (s : Fin R.boundaryCount → ℝ), IsInducedBoundaryOrientation R s →
        IntegrableOn (curvatureIntegrand g T c hc) R.carrier ∧
        (∀ i j, IntervalIntegrable (geodesicIntegrand g C o c hc (A i) j) volume 0 1) ∧
        (∀ i j, 0 < interiorAngle g o c hc (A i) (s i) j ∧
          interiorAngle g o c hc (A i) (s i) j < 2 * Real.pi) ∧
        (∀ i j, P202Specs.MetricBoundaryTurning.IsOccupiedSectorAngle
          g o c hc R i (A i) (s i) j (interiorAngle g o c hc (A i) (s i) j)) ∧
        (∃ h : P202Specs.EulerPoincare.HomologyFiniteType ℚ R.carrier,
          curvatureIntegral g T c hc R + geodesicIntegral g C o c hc R A s +
            exteriorAngleSum g o c hc R A s =
              2 * Real.pi * (P202Specs.EulerPoincare.topologicalEuler R.carrier h : ℝ)) ∧
        (R.boundaryCount = 1 →
          curvatureIntegral g T c hc R + geodesicIntegral g C o c hc R A s +
            exteriorAngleSum g o c hc R A s = 2 * Real.pi)

end Expected
end P202Specs.LocalGaussBonnet
