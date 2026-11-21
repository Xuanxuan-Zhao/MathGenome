import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PlaneTurning
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ChartRegionStokes
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SurfaceBoundaryGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Independent objects for paper.tex:4753–4758,4953–4970.
All tangent fields, curvature, frame coordinates, and the connection form
are the original intrinsic objects. No boundary or turning identity is a
frame hypothesis. The occupied-sector predicate below tests actual rays in
the original domain, away from the two limiting boundary rays. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators Classical ContDiff
namespace P202Specs.MetricBoundaryTurning
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
open P202.MetricData P202.ConnectionData P202.SurfaceBoundaryData
open P202Specs.PlanarRegionTopology P202Specs.PlaneTurning
universe u
variable {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M}

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

/-- Concrete hypotheses on an actual smooth local frame and three scalar
coefficient functions. In particular no geodesic-curvature identity or
integral/turning certificate is contained in these hypotheses. -/
structure FrameCoefficients (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    (a beta d : Plane → ℝ) : Prop where
  orthonormal : ∀ p i j, pairing g p.val (b.section_ i p) (b.section_ j p) =
    if i = j then 1 else 0
  positive : ∀ p, PositiveBoundaryOrientation o p.val (b.section_ 0 p) (b.section_ 1 p)
  smooth_a : ContDiffOn ℝ ∞ a (ChartRegionStokes.chartTarget c)
  smooth_beta : ContDiffOn ℝ ∞ beta (ChartRegionStokes.chartTarget c)
  smooth_d : ContDiffOn ℝ ∞ d (ChartRegionStokes.chartTarget c)
  pos_a : ∀ x ∈ ChartRegionStokes.chartTarget c, 0 < a x
  pos_d : ∀ x ∈ ChartRegionStokes.chartTarget c, 0 < d x
  coordinates : ∀ (x : Plane) (hx : x ∈ ChartRegionStokes.chartTarget c) (v : Plane),
    (b.basis ⟨chartPoint c x, c.map_target hx⟩).equivFun (chartVector c hc x v) =
      ![a x * v 0 + beta x * v 1, d x * v 1]

/-- Literal pullback of Gamma_10 by the actual inverse-chart differential. -/
def frameOneForm (C : Connection (tangentBundle S))
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source) :
    ChartRegionStokes.OneForm := fun x =>
  if hx : ChartRegionStokes.modelPoint x ∈ c.target then
    LinearMap.toContinuousLinearMap
      ((connectionForm C b ⟨chartPoint c x, c.map_target hx⟩ 1 0).comp
        (((tangentStructure S).fiberCoordinates.equiv c hc (chartPoint c x)
          (c.map_target hx)).symm.toLinearMap.comp
          (EuclideanSpace.equiv (Fin 2) ℝ).toLinearMap))
  else 0

/-- Frame coefficients of the actual normalized tangent on an extended arc. -/
def tangentCoefficients {q : RegularJordanCurve} (g : RiemannianMetric S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    (A : ArcPresentation q) (j : Fin A.count) : ℝ → Euclidean 2 :=
  P202.CurveConnectionData.coefficientsAlong b (surfaceArc c A j)
    (unitTangent g (surfaceArc c A j) (arcVelocity c hc A j))

/-- A genuine real angle lift of the actual frame coordinates. Its local
smoothness is a conclusion, not a field of this predicate. -/
def IsTangentAngle {q : RegularJordanCurve} (g : RiemannianMetric S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (b : LocalFrame (tangentBundle S) c.source c.open_source)
    (A : ArcPresentation q) (j : Fin A.count) (theta : ℝ → ℝ) (J : Set ℝ) : Prop :=
  ContinuousOn theta J ∧ ∀ t ∈ J,
    tangentCoefficients g c hc b A j t = ![Real.cos (theta t), Real.sin (theta t)]

/-- Positive metric angle, measured counterclockwise in (0,2*pi]. -/
def positiveMetricAngle (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (x u v : Plane) : ℝ := by
  let p := chartPoint c x
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  let r := ((planeOrientation g o p).oangle (chartVector c hc x u)
    (chartVector c hc x v)).toReal
  exact if 0 < r then r else r + 2 * Real.pi

/-- The forward ray at the vertex for the induced traversal. -/
def outgoingRay {q : RegularJordanCurve} (A : ArcPresentation q)
    (s : ℝ) (j : Fin A.count) : Plane :=
  if s = 1 then velocity A (finRotate A.count j) 0 else -velocity A j 1

/-- The other boundary ray points backwards along the incoming arc. -/
def incomingRay {q : RegularJordanCurve} (A : ArcPresentation q)
    (s : ℝ) (j : Fin A.count) : Plane :=
  if s = 1 then -velocity A j 1 else velocity A (finRotate A.count j) 0

/-- Geometric meaning of an occupied-sector angle: every nonboundary ray
points locally into the actual region exactly when its positive metric angle
from the outgoing ray is less than alpha. Boundary rays are excluded because
their exact straight rays can lie on either side of a curved boundary.
This distinguishes the reflex sector from the complementary convex sector. -/
def IsOccupiedSectorAngle (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (R : PlanarRegion) (i : Fin R.boundaryCount)
    (A : ArcPresentation (R.curve i)) (s : ℝ) (j : Fin A.count) (alpha : ℝ) : Prop :=
  0 < alpha ∧ alpha < 2 * Real.pi ∧ ∀ v : Plane, v ≠ 0 →
    NormedSpace.normalize v ≠ NormedSpace.normalize (outgoingRay A s j) →
    NormedSpace.normalize v ≠ NormedSpace.normalize (incomingRay A s j) →
    ((∀ᶠ r : ℝ in 𝓝[>] 0, A.arc j 1 + r • v ∈ R.domain) ↔
      positiveMetricAngle g o c hc (A.arc j 1) (outgoingRay A s j) v < alpha)

def upperTriangular (a b d : ℝ) : Plane →ₗ[ℝ] Plane where
  toFun v := !₂[a * v 0 + b * v 1, d * v 1]
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r v := by ext i; fin_cases i <;> simp <;> ring


namespace Expected

/-- The complete analytic component formula, including literal form
smoothness, intrinsic integrability and all principal corner terms. The
additional domain-sector interpretation is retained in `boundaryCalculus`. -/
def componentCalculus : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] (S : SmoothManifold 2 .euclidean M)
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)),
    P202.LeviCivitaData.IsLeviCivita g C →
    ∀ (o : SmoothManifolds.OrientationData.Orientation S)
      (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val),
    ChartRegionStokes.PositiveChart (P202.VolumeData.cotangentBundle S) o c hc →
    ∀ (b : LocalFrame (tangentBundle S) c.source c.open_source)
      (a beta d : Plane → ℝ), FrameCoefficients g o c hc b a beta d →
    ContDiffOn ℝ ∞ (frameOneForm C c hc b) (ChartRegionStokes.chartTarget c) ∧
    (∀ (q : RegularJordanCurve), q.trace ⊆ ChartRegionStokes.chartTarget c →
      ∀ A : ArcPresentation q,
        (∀ j t, t ∈ Icc (0 : ℝ) 1 →
          P202.CurveConnectionData.HasVelocityWithinAt S (surfaceArc c A j) univ t
            (arcVelocity c hc A j t) ∧ 0 < arcSpeed g c hc A j t) ∧
        (∀ j, P202.CurveData.CoordinateC1On S (surfaceArc c A j) (Icc (0 : ℝ) 1) ∧
          ContinuousOn (surfaceArc c A j) (Icc (0 : ℝ) 1) ∧
          P202.CurveConnectionData.C1FieldOn (B := tangentBundle S) (surfaceArc c A j)
            (unitTangent g (surfaceArc c A j) (arcVelocity c hc A j)) (Icc (0 : ℝ) 1)) ∧
        (∀ j, IntervalIntegrable (geodesicIntegrand g C o c hc A j) volume 0 1) ∧
        (∀ j t, t ∈ Icc (0 : ℝ) 1 →
          ∃ delta : ℝ, 0 < delta ∧ ∃ theta : ℝ → ℝ,
            IsTangentAngle g c hc b A j theta (Ioo (t-delta) (t+delta)) ∧
            ContDiffOn ℝ 1 theta (Ioo (t-delta) (t+delta))) ∧
        (∀ j (J : Set ℝ) (theta : ℝ → ℝ), IsOpen J → J ⊆ Ioo (0 : ℝ) 1 →
          IsTangentAngle g c hc b A j theta J →
          ∀ t ∈ J, HasDerivAt theta (deriv theta t) t ∧
            geodesicIntegrand g C o c hc A j t = deriv theta t +
              frameOneForm C c hc b (A.arc j t) (velocity A j t)) ∧
        (∀ (op : Orientation ℝ Plane (Fin 2)),
          (∀ v, op.rightAngleRotation v = quarterTurn v) →
          ∀ theta : AngleChoices op A,
            (∑ j, ∫ t in (0 : ℝ)..1, geodesicIntegrand g C o c hc A j t) +
              (∑ j, metricCornerAngle g o c hc A j) =
                totalTurning theta + ChartRegionStokes.componentIntegral (frameOneForm C c hc b) q))

/-- Full intrinsic boundary obligation, with explicit concrete frame input.
Every presentation and every continuous angle lift are quantified. Smooth
subdivision vertices have zero principal corner angle automatically. -/
def boundaryCalculus : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] (S : SmoothManifold 2 .euclidean M)
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)),
    P202.LeviCivitaData.IsLeviCivita g C →
    ∀ (o : SmoothManifolds.OrientationData.Orientation S)
      (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val),
    ChartRegionStokes.PositiveChart (P202.VolumeData.cotangentBundle S) o c hc →
    ∀ (b : LocalFrame (tangentBundle S) c.source c.open_source)
      (a beta d : Plane → ℝ), FrameCoefficients g o c hc b a beta d →
    ContDiffOn ℝ ∞ (frameOneForm C c hc b) (ChartRegionStokes.chartTarget c) ∧
    (∀ (q : RegularJordanCurve), q.trace ⊆ ChartRegionStokes.chartTarget c →
      ∀ A : ArcPresentation q,
        (∀ j t, t ∈ Icc (0 : ℝ) 1 →
          P202.CurveConnectionData.HasVelocityWithinAt S (surfaceArc c A j) univ t
            (arcVelocity c hc A j t) ∧ 0 < arcSpeed g c hc A j t) ∧
        (∀ j, P202.CurveData.CoordinateC1On S (surfaceArc c A j) (Icc (0 : ℝ) 1) ∧
          ContinuousOn (surfaceArc c A j) (Icc (0 : ℝ) 1) ∧
          P202.CurveConnectionData.C1FieldOn (B := tangentBundle S) (surfaceArc c A j)
            (unitTangent g (surfaceArc c A j) (arcVelocity c hc A j)) (Icc (0 : ℝ) 1)) ∧
        (∀ j, IntervalIntegrable (geodesicIntegrand g C o c hc A j) volume 0 1) ∧
        (∀ j t, t ∈ Icc (0 : ℝ) 1 →
          ∃ delta : ℝ, 0 < delta ∧ ∃ theta : ℝ → ℝ,
            IsTangentAngle g c hc b A j theta (Ioo (t-delta) (t+delta)) ∧
            ContDiffOn ℝ 1 theta (Ioo (t-delta) (t+delta))) ∧
        (∀ j (J : Set ℝ) (theta : ℝ → ℝ), IsOpen J → J ⊆ Ioo (0 : ℝ) 1 →
          IsTangentAngle g c hc b A j theta J →
          ∀ t ∈ J, HasDerivAt theta (deriv theta t) t ∧
            geodesicIntegrand g C o c hc A j t = deriv theta t +
              frameOneForm C c hc b (A.arc j t) (velocity A j t)) ∧
        (∀ (op : Orientation ℝ Plane (Fin 2)),
          (∀ v, op.rightAngleRotation v = quarterTurn v) →
          ∀ theta : AngleChoices op A,
            (∑ j, ∫ t in (0 : ℝ)..1, geodesicIntegrand g C o c hc A j t) +
              (∑ j, metricCornerAngle g o c hc A j) =
                totalTurning theta + ChartRegionStokes.componentIntegral (frameOneForm C c hc b) q)) ∧
    (∀ (R : PlanarRegion), R.carrier ⊆ ChartRegionStokes.chartTarget c →
      ∀ (s : Fin R.boundaryCount → ℝ), IsInducedBoundaryOrientation R s →
      ∀ (i : Fin R.boundaryCount) (A : ArcPresentation (R.curve i)) (j : Fin A.count),
        IsOccupiedSectorAngle g o c hc R i A (s i) j
          (interiorAngle g o c hc A (s i) j))


/-- The arc-calculus part of the boundary theorem, stated separately so the
proved intrinsic regularity and pointwise formula can be reused while the
integral and occupied-sector conclusions are completed. -/
def arcCalculus : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] (S : SmoothManifold 2 .euclidean M)
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)),
    P202.LeviCivitaData.IsLeviCivita g C →
    ∀ (o : SmoothManifolds.OrientationData.Orientation S)
      (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
      (b : LocalFrame (tangentBundle S) c.source c.open_source)
      (a beta d : Plane → ℝ), FrameCoefficients g o c hc b a beta d →
    ∀ (q : RegularJordanCurve), q.trace ⊆ ChartRegionStokes.chartTarget c →
      ∀ A : ArcPresentation q,
        (∀ j t, t ∈ Icc (0 : ℝ) 1 →
          P202.CurveConnectionData.HasVelocityWithinAt S (surfaceArc c A j) univ t
            (arcVelocity c hc A j t) ∧ 0 < arcSpeed g c hc A j t ∧
          ∃ D, P202.CurveConnectionData.HasCovariantDerivativeAt C (surfaceArc c A j)
            (unitTangent g (surfaceArc c A j) (arcVelocity c hc A j)) t D) ∧
        (∀ j, P202.CurveData.CoordinateC1On S (surfaceArc c A j) (Icc (0 : ℝ) 1) ∧
          ContinuousOn (surfaceArc c A j) (Icc (0 : ℝ) 1) ∧
          P202.CurveConnectionData.C1FieldOn (B := tangentBundle S) (surfaceArc c A j)
            (unitTangent g (surfaceArc c A j) (arcVelocity c hc A j)) (Icc (0 : ℝ) 1)) ∧
        (∀ j t, t ∈ Icc (0 : ℝ) 1 →
          ∃ delta : ℝ, 0 < delta ∧ ∃ theta : ℝ → ℝ,
            IsTangentAngle g c hc b A j theta (Ioo (t-delta) (t+delta)) ∧
            ContDiffOn ℝ 1 theta (Ioo (t-delta) (t+delta))) ∧
        (∀ j (J : Set ℝ) (theta : ℝ → ℝ), IsOpen J → J ⊆ Ioo (0 : ℝ) 1 →
          IsTangentAngle g c hc b A j theta J →
          ∀ t ∈ J, HasDerivAt theta (deriv theta t) t ∧
            geodesicIntegrand g C o c hc A j t = deriv theta t +
              frameOneForm C c hc b (A.arc j t) (velocity A j t))

/-- Full finite turning invariance, including every actual principal short
corner. Endpoint coefficients agree at each cyclic join; no angle increment,
winding value or transformed-corner equality is assumed. -/
def triangularTurning : Prop := ∀ {ι : Type u} [Fintype ι]
    (o : Orientation ℝ Plane (Fin 2)) (rotateIndex : Equiv.Perm ι)
    (v w : ι → Plane), (∀ i, v i ≠ 0) → (∀ i, w i ≠ 0) →
    (∀ i, NormedSpace.normalize (w i) ≠ -NormedSpace.normalize (v (rotateIndex i))) →
    ∀ (a0 beta0 d0 a1 beta1 d1 : ι → ℝ),
    (∀ i, 0 < a1 i) → (∀ i, 0 < d1 i) →
    (∀ i, a1 i = a0 (rotateIndex i) ∧ beta1 i = beta0 (rotateIndex i) ∧ d1 i = d0 (rotateIndex i)) →
    ∀ (start finish : ι → ℝ),
    (∑ i, ((finish i + (o.oangle (w i) (upperTriangular (a1 i) (beta1 i) (d1 i) (w i))).toReal) -
      (start i + (o.oangle (v i) (upperTriangular (a0 i) (beta0 i) (d0 i) (v i))).toReal) +
      (o.oangle (upperTriangular (a1 i) (beta1 i) (d1 i) (w i))
        (upperTriangular (a1 i) (beta1 i) (d1 i) (v (rotateIndex i)))).toReal)) =
      ∑ i, (finish i - start i + (o.oangle (w i) (v (rotateIndex i))).toReal)

end Expected
end P202Specs.MetricBoundaryTurning
