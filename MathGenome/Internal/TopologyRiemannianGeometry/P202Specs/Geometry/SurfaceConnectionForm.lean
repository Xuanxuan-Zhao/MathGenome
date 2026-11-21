import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ChartRegionStokes
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SurfaceBoundaryGeometry
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CurvatureAlgebra

/-! Independent literal chart formulas for the moving-frame calculation in
paper.tex 4937–4951. No frame or curvature identity is an input certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
open Set
open scoped ContDiff Classical
namespace P202Specs.SurfaceConnectionForm
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
open SmoothManifolds.BundleData SmoothManifolds.BundleOperationsData
open P202.MetricData P202.ConnectionData P202.CurvatureData P202.SurfaceBoundaryData
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

/-- The basis is the inverse of the actual tangent coordinate isomorphism. -/
def coordinateBasis (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    Module.Basis (Fin 2) ℝ (TangentSpace S p.val) :=
  (Pi.basisFun ℝ (Fin 2)).map
    ((tangentStructure S).fiberCoordinates.equiv c hc p.val p.property).symm

def gramE (g : RiemannianMetric S) (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (x : Plane) : ℝ :=
  pairing g (chartPoint c x)
    (chartVector c hc x (ChartRegionStokes.coordinateFrame 0))
    (chartVector c hc x (ChartRegionStokes.coordinateFrame 0))

def gramF (g : RiemannianMetric S) (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (x : Plane) : ℝ :=
  pairing g (chartPoint c x)
    (chartVector c hc x (ChartRegionStokes.coordinateFrame 0))
    (chartVector c hc x (ChartRegionStokes.coordinateFrame 1))

def gramG (g : RiemannianMetric S) (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (x : Plane) : ℝ :=
  pairing g (chartPoint c x)
    (chartVector c hc x (ChartRegionStokes.coordinateFrame 1))
    (chartVector c hc x (ChartRegionStokes.coordinateFrame 1))

def triangularA (g : RiemannianMetric S) (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) : Plane → ℝ := fun x => Real.sqrt (gramE g c hc x)

def triangularBeta (g : RiemannianMetric S) (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) : Plane → ℝ := fun x => gramF g c hc x / triangularA g c hc x

def triangularD (g : RiemannianMetric S) (c : ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val) : Plane → ℝ := fun x =>
  Real.sqrt (gramG g c hc x - gramF g c hc x ^ 2 / gramE g c hc x)

/-- Literal pullback of Gamma_10, totalized by zero outside the open target. -/
def omega (C : Connection (tangentBundle S))
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source) : ChartRegionStokes.OneForm :=
  fun x => if hx : ChartRegionStokes.modelPoint x ∈ c.target then
    LinearMap.toContinuousLinearMap
      ((connectionForm C b ⟨chartPoint c x, c.map_target hx⟩ 1 0).comp
        (((tangentStructure S).fiberCoordinates.equiv c hc (chartPoint c x)
          (c.map_target hx)).symm.toLinearMap.comp
          (EuclideanSpace.equiv (Fin 2) ℝ).toLinearMap))
  else 0

/-- Full chart-frame properties, with Gram–Schmidt specified on the actual
coordinate basis rather than an abstract orthonormal witness. -/
def IsChartFrame (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source) : Prop :=
  (∀ p : c.source, b.section_ 0 p =
    (tangentNorm g p.val (coordinateBasis c hc p 0))⁻¹ • coordinateBasis c hc p 0) ∧
  (∀ p : c.source, let r := coordinateBasis c hc p 1 +
      (-(pairing g p.val (coordinateBasis c hc p 0) (coordinateBasis c hc p 1) /
        pairing g p.val (coordinateBasis c hc p 0) (coordinateBasis c hc p 0))) •
          coordinateBasis c hc p 0
    b.section_ 1 p = (tangentNorm g p.val r)⁻¹ • r) ∧
  (∀ p i j, pairing g p.val (b.section_ i p) (b.section_ j p) = if i = j then 1 else 0) ∧
  (∀ p : c.source, SmoothManifolds.OrientationData.IsPositive (o.val p.val)
    (exteriorPower.ιMulti ℝ 2 (b.basis p))) ∧
  ContDiffOn ℝ ∞ (triangularA g c hc) (ChartRegionStokes.chartTarget c) ∧
  ContDiffOn ℝ ∞ (triangularBeta g c hc) (ChartRegionStokes.chartTarget c) ∧
  ContDiffOn ℝ ∞ (triangularD g c hc) (ChartRegionStokes.chartTarget c) ∧
  (∀ x, ∀ hx : x ∈ ChartRegionStokes.chartTarget c,
    0 < triangularA g c hc x ∧ 0 < triangularD g c hc x ∧
    triangularA g c hc x * triangularD g c hc x = areaWeight g c hc x ∧
    ∀ v : Plane, (b.basis ⟨chartPoint c x, c.map_target hx⟩).equivFun
      (chartVector c hc x v) =
        ![triangularA g c hc x * v 0 + triangularBeta g c hc x * v 1,
          triangularD g c hc x * v 1])

namespace Expected
/-- The original unconditional moving-frame construction and curvature density
identity. The metric determinant and sectional quotient keep their original values. -/
def surfaceConnectionForm : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] (S : SmoothManifold 2 .euclidean M)
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)),
    P202.LeviCivitaData.IsLeviCivita g C →
    ∀ (T : CurvatureTensor S), RepresentsCurvature C T →
    ∀ (o : SmoothManifolds.OrientationData.Orientation S)
      (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val),
      ChartRegionStokes.PositiveChart (P202.VolumeData.cotangentBundle S) o c hc →
    ∃ b : LocalFrame (tangentBundle S) c.source c.open_source,
      IsChartFrame g o c hc b ∧
      ContDiffOn ℝ ∞ (omega C c hc b) (ChartRegionStokes.chartTarget c) ∧
      ∀ x ∈ ChartRegionStokes.chartTarget c,
        ChartRegionStokes.exteriorCoefficient (omega C c hc b) x =
          -gaussianCurvature g T (chartPoint c x) * areaWeight g c hc x
end Expected
end P202Specs.SurfaceConnectionForm
