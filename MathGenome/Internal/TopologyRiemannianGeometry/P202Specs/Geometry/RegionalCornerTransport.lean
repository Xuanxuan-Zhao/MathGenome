import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GlobalGaussBonnetLocalization
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Module.Ray
import Mathlib.Analysis.Convex.PathConnected

/-! Independent interface for regional corner transport.
All statements retain the canonical original objects, arbitrary presentations,
both model kinds, and actual atlas and domain-ray germs. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open Complex (arg)
open scoped BigOperators _root_.Topology
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleOperationsData
  SmoothManifolds.TangentBundleData
open P202.MetricData P202.SurfaceBoundaryData
open P202Specs.PlanarRegionTopology P202Specs.MetricBoundaryTurning P202Specs.PlaneTurning
open P202Specs.SurfaceRegionConstruction P202Specs.SurfaceRegionsEuler
open P202Specs.GlobalGaussBonnet
namespace P202Specs.RegionalCornerTransport
open SmoothManifolds (ModelKind)
universe u

def positiveAngle (theta : Real.Angle) : ℝ :=
  if 0 < theta.toReal then theta.toReal else theta.toReal + 2 * Real.pi

def tangentAngle
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S) (p : M)
    (o : Orientation ℝ (TangentSpace S p) (Fin 2))
    (u v : TangentSpace S p) : Real.Angle := by
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  exact o.oangle u v


/-- Metric area form in the original two-dimensional tangent fiber. -/
def tangentArea
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S) (p : M)
    (o : Orientation ℝ (TangentSpace S p) (Fin 2))
    (u v : TangentSpace S p) : ℝ := by
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  exact o.areaForm u v

def sector (r a b : ℝ) : Set ℂ :=
  {z | z ≠ 0 ∧ ‖z‖ < r ∧ Complex.arg z ∈ Ioo a b}


/-- The occupied-ray test in the original tangent fiber and the original
complementary component. Only its expression changes: domain rays are literal
coordinate rays and the metric angle is evaluated in the original g fiber. -/
def originalOccupiedSectorAngle
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (p : M) (hp : p ∈ (D.chart r).source)
    (o : Orientation ℝ (TangentSpace S p) (Fin 2))
    (i : Fin (D.region r).boundaryCount) (A : ArcPresentation ((D.region r).curve i))
    (s : ℝ) (j : Fin A.count) (alpha : ℝ) (reversed : Bool) : Prop :=
  let K := (tangentStructure S).fiberCoordinates.equiv (D.chart r) (D.chart_mem r) p hp
  let V := fun v : Plane => K.symm (EuclideanSpace.equiv (Fin 2) ℝ v)
  0 < alpha ∧ alpha < 2 * Real.pi ∧ ∀ v : Plane, v ≠ 0 →
    NormedSpace.normalize v ≠ NormedSpace.normalize (outgoingRay A s j) →
    NormedSpace.normalize v ≠ NormedSpace.normalize (incomingRay A s j) →
    ((∀ᶠ t : ℝ in 𝓝[>] 0, ∃ q ∈ regionInterior D r,
        coordinates (D.chart r) q = A.arc j 1 + t • v) ↔
      (if reversed then positiveAngle (tangentAngle g p o (V v) (V (outgoingRay A s j)))
      else positiveAngle (tangentAngle g p o (V (outgoingRay A s j)) (V v))) < alpha)

/-- Coordinates with the argument cut on the specified nonzero boundary ray. -/
def branchCoordinate (u z : ℂ) : ℂ := -star u * z

/-- The explicit counterclockwise sector from u to w. Its angular cut is
one of its two boundary rays. -/
def raySector (r : ℝ) (u w : ℂ) : Set ℂ :=
  {z | branchCoordinate u z ≠ 0 ∧ ‖branchCoordinate u z‖ < r ∧
    Complex.arg (branchCoordinate u z) ∈
      Ioo (-Real.pi) (Complex.arg (branchCoordinate u w))}

/-- Center and the specified finite family of closed positive rays. -/
def closedRays {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (d : Fin n → E) : Set E :=
  {0} ∪ ⋃ i, (fun r : ℝ => r • d i) '' Ici 0

/-- The original chart model centered at an actual graph star. -/
def centeredModel {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {G : EmbeddedGraph S} {p : M}
    (g : GraphStar G p) : Set Plane :=
  {z | toPlane.symm (coordinates g.chart p + z) ∈ modelSet 2 kind}

attribute [local instance] Complex.finrank_real_complex_fact

namespace Expected
def metricCornerAngle_eq_at_common_endpoint : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M} {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A B : ArcPresentation q) (j : Fin A.count) (k : Fin B.count)
    (hp : A.arc j 1 = B.arc k 1),
    P202Specs.LocalGaussBonnet.metricCornerAngle g o c hc A j =
      P202Specs.LocalGaussBonnet.metricCornerAngle g o c hc B k

def metricCornerAngle_eq_zero_of_endpoint_unlisted : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M} {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A B : ArcPresentation q) (j : Fin A.count)
    (hne : ∀ k : Fin B.count, A.arc j 1 ≠ B.arc k 1),
    P202Specs.LocalGaussBonnet.metricCornerAngle g o c hc A j = 0

def sum_metricCornerAngle_eq : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M} {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A B : ArcPresentation q),
    (∑ j, P202Specs.LocalGaussBonnet.metricCornerAngle g o c hc A j) =
      ∑ k, P202Specs.LocalGaussBonnet.metricCornerAngle g o c hc B k

def exteriorAngleSum_eq_of_presentations : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M} (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (R : PlanarRegion) (A B : ∀ i, ArcPresentation (R.curve i))
    (s : Fin R.boundaryCount → ℝ),
    P202Specs.LocalGaussBonnet.exteriorAngleSum g o c hc R A s =
      P202Specs.LocalGaussBonnet.exteriorAngleSum g o c hc R B s

def regionalChartGeometry_pairing_coordinateVectors : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (G : RegionalChartGeometry g D r) (p : G.neighborhood) (v w : Euclidean 2),
    pairing G.metric (G.map p)
      (((tangentStructure G.ambientSurface).fiberCoordinates.equiv
        G.ambientChart G.ambientChart_mem (G.map p)
        (by rw [G.ambientChart_source]; trivial)).symm v)
      (((tangentStructure G.ambientSurface).fiberCoordinates.equiv
        G.ambientChart G.ambientChart_mem (G.map p)
        (by rw [G.ambientChart_source]; trivial)).symm w) =
    pairing g p.val
      (((tangentStructure S).fiberCoordinates.equiv
        (D.chart r) (D.chart_mem r) p.val (G.source_subset p.property)).symm v)
      (((tangentStructure S).fiberCoordinates.equiv
        (D.chart r) (D.chart_mem r) p.val (G.source_subset p.property)).symm w)

def regionalChartGeometry_angle_transport : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (G : RegionalChartGeometry g D r) (p : G.neighborhood)
    (o : Orientation ℝ (TangentSpace S p.val) (Fin 2)),
    let K := (tangentStructure S).fiberCoordinates.equiv
      (D.chart r) (D.chart_mem r) p.val (G.source_subset p.property)
    let F := (tangentStructure G.ambientSurface).fiberCoordinates.equiv
      G.ambientChart G.ambientChart_mem (G.map p)
      (by rw [G.ambientChart_source]; trivial)
    (∀ u v : Euclidean 2,
      tangentAngle G.metric (G.map p) (planeOrientation G.metric G.orientation (G.map p))
        (F.symm u) (F.symm v) = tangentAngle g p.val o (K.symm u) (K.symm v)) ∨
    (∀ u v : Euclidean 2,
      tangentAngle G.metric (G.map p) (planeOrientation G.metric G.orientation (G.map p))
        (F.symm u) (F.symm v) = tangentAngle g p.val o (K.symm v) (K.symm u))

def regionalChartGeometry_modelPoint : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (G : RegionalChartGeometry g D r) (p : G.neighborhood),
    P202Specs.ChartRegionStokes.modelPoint (coordinates (D.chart r) p.val) =
      G.ambientChart (G.map p)

def regionalChartGeometry_chartPoint : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (G : RegionalChartGeometry g D r) (p : G.neighborhood),
    chartPoint G.ambientChart (coordinates (D.chart r) p.val) = G.map p

def regionalChartGeometry_chartVector : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (G : RegionalChartGeometry g D r) (p : G.neighborhood) (v : Plane),
    HEq (chartVector G.ambientChart G.ambientChart_mem (coordinates (D.chart r) p.val) v)
      (((tangentStructure G.ambientSurface).fiberCoordinates.equiv
        G.ambientChart G.ambientChart_mem (G.map p)
        (by rw [G.ambientChart_source]; trivial)).symm (EuclideanSpace.equiv (Fin 2) ℝ v))

def regionalChartGeometry_positiveMetricAngle_transport : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (G : RegionalChartGeometry g D r) (p : G.neighborhood)
    (o : Orientation ℝ (TangentSpace S p.val) (Fin 2)),
    let K := (tangentStructure S).fiberCoordinates.equiv
      (D.chart r) (D.chart_mem r) p.val (G.source_subset p.property)
    (∀ u v : Plane,
      positiveMetricAngle G.metric G.orientation G.ambientChart G.ambientChart_mem
        (coordinates (D.chart r) p.val) u v = positiveAngle
          (tangentAngle g p.val o
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ u))
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ v)))) ∨
    (∀ u v : Plane,
      positiveMetricAngle G.metric G.orientation G.ambientChart G.ambientChart_mem
        (coordinates (D.chart r) p.val) u v = positiveAngle
          (tangentAngle g p.val o
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ v))
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ u))))

def eventually_sector_iff_of_hasDerivAt : Prop :=
  ∀ {F : ℝ → ℂ} {v : ℂ} {r a b : ℝ}
    (hF : HasDerivAt F v 0) (h0 : F 0 = 0) (hr : 0 < r)
    (hv : v ∈ Complex.slitPlane) (ha : arg v ≠ a) (hb : arg v ≠ b),
    ∀ᶠ t : ℝ in 𝓝[>] 0, (F t ∈ sector r a b ↔ arg v ∈ Ioo a b)

def eventually_sector_iff_derivative_ray : Prop :=
  ∀ {F : ℝ → ℂ} {v : ℂ} {r a b : ℝ}
    (hF : HasDerivAt F v 0) (h0 : F 0 = 0) (hr : 0 < r)
    (hv : v ∈ Complex.slitPlane) (ha : arg v ≠ a) (hb : arg v ≠ b),
    ∀ᶠ t : ℝ in 𝓝[>] 0, (F t ∈ sector r a b ↔ t • v ∈ sector r a b)

def smoothJoin_exterior_contribution_zero : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M} {q : RegularJordanCurve}
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (A : ArcPresentation q) (s : ℝ) (j : Fin A.count)
    (hd : DifferentiableAt ℝ (realLift q.parametrization) (A.time j.succ)),
    Real.pi - P202Specs.LocalGaussBonnet.interiorAngle g o c hc A s j = 0

def oangle_isometry_order_selection : Prop :=
  ∀ {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [Fact (Module.finrank ℝ E = 2)] [Fact (Module.finrank ℝ F = 2)] (L : E ≃ₗ[ℝ] F) (hm : ∀ u v, inner ℝ (L u) (L v) = inner ℝ u v)
    (oE : Orientation ℝ E (Fin 2)) (oF : Orientation ℝ F (Fin 2))
    (a b : E) (hE : 0 < oE.areaForm a b),
    (0 < oF.areaForm (L a) (L b) ∨ oF.areaForm (L a) (L b) < 0) ∧
    (0 < oF.areaForm (L a) (L b) →
      ∀ u v, oF.oangle (L u) (L v) = oE.oangle u v) ∧
    (oF.areaForm (L a) (L b) < 0 →
      ∀ u v, oF.oangle (L u) (L v) = oE.oangle v u)

def regionalChartGeometry_metricCornerAngle_transport : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (G : RegionalChartGeometry g D r) (p : G.neighborhood)
    (o : Orientation ℝ (TangentSpace S p.val) (Fin 2)),
    let K := (tangentStructure S).fiberCoordinates.equiv
      (D.chart r) (D.chart_mem r) p.val (G.source_subset p.property)
    (∀ (q : RegularJordanCurve) (A : ArcPresentation q) (j : Fin A.count),
      A.arc j 1 = coordinates (D.chart r) p.val →
      P202Specs.LocalGaussBonnet.metricCornerAngle G.metric G.orientation
        G.ambientChart G.ambientChart_mem A j =
          (tangentAngle g p.val o
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ (velocity A j 1)))
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ
              (velocity A (finRotate A.count j) 0)))).toReal) ∨
    (∀ (q : RegularJordanCurve) (A : ArcPresentation q) (j : Fin A.count),
      A.arc j 1 = coordinates (D.chart r) p.val →
      P202Specs.LocalGaussBonnet.metricCornerAngle G.metric G.orientation
        G.ambientChart G.ambientChart_mem A j =
          (tangentAngle g p.val o
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ
              (velocity A (finRotate A.count j) 0)))
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ (velocity A j 1)))).toReal)

def exists_atlas_transition_extension : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n kind M) (K : FiberCoordinates S)
    (e d : ModelChart n kind M) (he : e ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : M)
    (hp : p ∈ e.source) (hpd : p ∈ d.source),
    ∃ (U : Set (Euclidean n)) (F : Euclidean n → Euclidean n),
      IsOpen U ∧ (e p).val ∈ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
      F (e p).val = (d p).val ∧
      HasFDerivAt F (fderiv ℝ F (e p).val) (e p).val ∧
      (∀ q (hq : q ∈ e.source) (hqd : q ∈ d.source), (e q).val ∈ U →
        F (e q).val = (d q).val) ∧
      (∀ v, fderiv ℝ F (e p).val v =
        K.equiv d hd p hpd ((K.equiv e he p hp).symm v))

def hasDerivAt_transition_ray : Prop :=
  ∀ {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {L : E →L[ℝ] F} {x : E} (hf : HasFDerivAt f L x) (v : E),
    HasDerivAt (fun t : ℝ => f (x + t • v) - f x) (L v) 0

def eventually_cone_iff_of_hasFDerivAt : Prop :=
  ∀ {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {L : E →L[ℝ] F} {x : E} (hf : HasFDerivAt f L x)
    (v : E) (C : F →L[ℝ] ℂ) {r a b : ℝ} (hr : 0 < r)
    (hv : C (L v) ∈ Complex.slitPlane)
    (ha : Complex.arg (C (L v)) ≠ a) (hb : Complex.arg (C (L v)) ≠ b),
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      (C (f (x + t • v) - f x) ∈ sector r a b ↔
        t • C (L v) ∈ sector r a b)

def exists_atlas_transition_extension_with_cones : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 2 kind M) (K : SmoothManifolds.TangentBundleData.FiberCoordinates S)
    (e d : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : M)
    (hp : p ∈ e.source) (hpd : p ∈ d.source),
    ∃ (U : Set (Euclidean 2)) (F : Euclidean 2 → Euclidean 2),
      IsOpen U ∧ (e p).val ∈ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
      F (e p).val = (d p).val ∧
      (∀ q (hq : q ∈ e.source) (hqd : q ∈ d.source), (e q).val ∈ U →
        F (e q).val = (d q).val) ∧
      (∀ v, fderiv ℝ F (e p).val v =
        K.equiv d hd p hpd ((K.equiv e he p hp).symm v)) ∧
      (∀ (v : Euclidean 2) (C : Euclidean 2 →L[ℝ] ℂ) (r a b : ℝ),
        let w := K.equiv d hd p hpd ((K.equiv e he p hp).symm v)
        0 < r → C w ∈ Complex.slitPlane →
        Complex.arg (C w) ≠ a → Complex.arg (C w) ≠ b →
        ∀ᶠ t : ℝ in 𝓝[>] 0,
          (C (F ((e p).val + t • v) - (d p).val) ∈ sector r a b ↔
            t • C w ∈ sector r a b))

def exists_atlas_transition_localDiffeomorph : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n kind M) (K : SmoothManifolds.TangentBundleData.FiberCoordinates S)
    (e d : ModelChart n kind M) (he : e ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : M)
    (hp : p ∈ e.source) (hpd : p ∈ d.source),
    let L := ((K.equiv e he p hp).symm.trans (K.equiv d hd p hpd)).toContinuousLinearEquiv
    ∃ H : OpenPartialHomeomorph (Euclidean n) (Euclidean n),
      (e p).val ∈ H.source ∧ H (e p).val = (d p).val ∧
      ContDiffAt ℝ (⊤ : ℕ∞) H (e p).val ∧
      ContDiffAt ℝ (⊤ : ℕ∞) H.symm (d p).val ∧
      HasFDerivAt H (L : Euclidean n →L[ℝ] Euclidean n) (e p).val ∧
      HasFDerivAt H.symm (L.symm : Euclidean n →L[ℝ] Euclidean n) (d p).val ∧
      ((fun q => H (e q).val) =ᶠ[𝓝 p] (fun q => (d q).val)) ∧
      ((fun q => H.symm (d q).val) =ᶠ[𝓝 p] (fun q => (e q).val))

def eventually_image_cone_iff_inverse_derivative : Prop :=
  ∀ {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : OpenPartialHomeomorph E F) (x : E) (hx : x ∈ H.source)
    {L : F →L[ℝ] E} (hder : HasFDerivAt H.symm L (H x))
    (v : F) (C : E →L[ℝ] ℂ) {r a b : ℝ} (hr : 0 < r)
    (hv : C (L v) ∈ Complex.slitPlane)
    (ha : Complex.arg (C (L v)) ≠ a) (hb : Complex.arg (C (L v)) ≠ b),
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      (H x + t • v ∈ H '' (H.source ∩ (fun z => C (z - x)) ⁻¹' sector r a b) ↔
        t • C (L v) ∈ sector r a b)

def regionalChartGeometry_occupiedSectorAngle_transport : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (G : RegionalChartGeometry g D r) (p : G.neighborhood)
    (o : Orientation ℝ (TangentSpace S p.val) (Fin 2))
    (A : ∀ i, ArcPresentation ((D.region r).curve i))
    (s : Fin (D.region r).boundaryCount → ℝ)
    (hs : IsInducedBoundaryOrientation (D.region r) s)
    (i : Fin (D.region r).boundaryCount) (j : Fin (A i).count)
    (hj : (A i).arc j 1 = coordinates (D.chart r) p.val),
    ∃ reversed : Bool,
      originalOccupiedSectorAngle g D r p.val (G.source_subset p.property) o i (A i) (s i) j
        (P202Specs.LocalGaussBonnet.interiorAngle G.metric G.orientation
          G.ambientChart G.ambientChart_mem (A i) (s i) j) reversed

def regionalChartGeometry_order_selection : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (G : RegionalChartGeometry g D r) (p : G.neighborhood)
    (o : Orientation ℝ (TangentSpace S p.val) (Fin 2))
    (a b : TangentSpace S p.val) (hpos : 0 < tangentArea g p.val o a b),
    let K := (tangentStructure S).fiberCoordinates.equiv
      (D.chart r) (D.chart_mem r) p.val (G.source_subset p.property)
    let F := (tangentStructure G.ambientSurface).fiberCoordinates.equiv
      G.ambientChart G.ambientChart_mem (G.map p)
      (by rw [G.ambientChart_source]; trivial)
    let delta := tangentArea G.metric (G.map p)
      (planeOrientation G.metric G.orientation (G.map p)) (F.symm (K a)) (F.symm (K b))
    (0 < delta ∨ delta < 0) ∧
    (0 < delta → ∀ u v : Plane,
      positiveMetricAngle G.metric G.orientation G.ambientChart G.ambientChart_mem
        (coordinates (D.chart r) p.val) u v = positiveAngle
          (tangentAngle g p.val o
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ u))
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ v)))) ∧
    (delta < 0 → ∀ u v : Plane,
      positiveMetricAngle G.metric G.orientation G.ambientChart G.ambientChart_mem
        (coordinates (D.chart r) p.val) u v = positiveAngle
          (tangentAngle g p.val o
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ v))
            (K.symm (EuclideanSpace.equiv (Fin 2) ℝ u))))

def exists_atlas_transition_with_cone_images : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 2 kind M) (K : SmoothManifolds.TangentBundleData.FiberCoordinates S)
    (e d : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : M)
    (hp : p ∈ e.source) (hpd : p ∈ d.source),
    let L := ((K.equiv e he p hp).symm.trans (K.equiv d hd p hpd)).toContinuousLinearEquiv
    ∃ H : OpenPartialHomeomorph (Euclidean 2) (Euclidean 2),
      (e p).val ∈ H.source ∧ H (e p).val = (d p).val ∧
      ContDiffAt ℝ (⊤ : ℕ∞) H (e p).val ∧
      ContDiffAt ℝ (⊤ : ℕ∞) H.symm (d p).val ∧
      ((fun q => H (e q).val) =ᶠ[𝓝 p] (fun q => (d q).val)) ∧
      ((fun q => H.symm (d q).val) =ᶠ[𝓝 p] (fun q => (e q).val)) ∧
      (∀ (v : Euclidean 2) (C : Euclidean 2 →L[ℝ] ℂ) (r a b : ℝ),
        0 < r → C (L.symm v) ∈ Complex.slitPlane →
        Complex.arg (C (L.symm v)) ≠ a → Complex.arg (C (L.symm v)) ≠ b →
        ∀ᶠ t : ℝ in 𝓝[>] 0,
          ((d p).val + t • v ∈
            H '' (H.source ∩ (fun z => C (z - (e p).val)) ⁻¹' sector r a b) ↔
            t • C (L.symm v) ∈ sector r a b))

def eventually_raySector_iff_derivative_ray : Prop :=
  ∀
    {F : ℝ → ℂ} {v u w : ℂ} {r : ℝ}
    (hF : HasDerivAt F v 0) (h0 : F 0 = 0) (hr : 0 < r)
    (hu : u ≠ 0) (hw : w ≠ 0) (hv : v ≠ 0)
    (hvu : ¬SameRay ℝ v u) (hvw : ¬SameRay ℝ v w),
    ∀ᶠ t : ℝ in 𝓝[>] 0, (F t ∈ raySector r u w ↔ t • v ∈ raySector r u w)

def eventually_rayCone_iff_of_hasFDerivAt : Prop :=
  ∀
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {L : E →L[ℝ] F} {x : E} (hf : HasFDerivAt f L x)
    (v : E) (C : F →L[ℝ] ℂ) {r : ℝ} {u w : ℂ} (hr : 0 < r)
    (hu : u ≠ 0) (hw : w ≠ 0) (hv : C (L v) ≠ 0)
    (hvu : ¬SameRay ℝ (C (L v)) u) (hvw : ¬SameRay ℝ (C (L v)) w),
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      (C (f (x + t • v) - f x) ∈ raySector r u w ↔
        t • C (L v) ∈ raySector r u w)

def eventually_image_rayCone_iff_inverse_derivative : Prop :=
  ∀
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : OpenPartialHomeomorph E F) (x : E) (hx : x ∈ H.source)
    {L : F →L[ℝ] E} (hder : HasFDerivAt H.symm L (H x))
    (v : F) (C : E →L[ℝ] ℂ) {r : ℝ} {u w : ℂ} (hr : 0 < r)
    (hu : u ≠ 0) (hw : w ≠ 0) (hv : C (L v) ≠ 0)
    (hvu : ¬SameRay ℝ (C (L v)) u) (hvw : ¬SameRay ℝ (C (L v)) w),
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      (H x + t • v ∈ H '' (H.source ∩ (fun z => C (z - x)) ⁻¹' raySector r u w) ↔
        t • C (L v) ∈ raySector r u w)

def coordinateImage_inter_nhds : Prop :=
  ∀
    {n : ℕ} {kind : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
    (d : ModelChart n kind M) (p : M) (hp : p ∈ d.source)
    (W : Set M) (hW : IsOpen W) (hpW : p ∈ W)
    (A : Set M) (hA : A ⊆ d.source),
    ∀ᶠ y : Euclidean n in 𝓝 (d p).val,
      (y ∈ (fun q => (d q).val) '' A ↔
        y ∈ (fun q => (d q).val) '' (A ∩ W))

def exists_coordinateImage_germ : Prop :=
  ∀
    {n : ℕ} {kind : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
    (e d : ModelChart n kind M) (p : M)
    (hp : p ∈ e.source) (hpd : p ∈ d.source)
    (H : OpenPartialHomeomorph (Euclidean n) (Euclidean n))
    (hx : (e p).val ∈ H.source)
    (hrep : (fun q => H (e q).val) =ᶠ[𝓝 p] (fun q => (d q).val)),
    ∃ W : Set M, IsOpen W ∧ p ∈ W ∧ W ⊆ e.source ∩ d.source ∧
      (∀ q ∈ W, (e q).val ∈ H.source) ∧
      ∀ A : Set M, A ⊆ d.source → ∀ᶠ y : Euclidean n in 𝓝 (d p).val,
        (y ∈ (fun q => (d q).val) '' A ↔
          y ∈ H '' ((fun q => (e q).val) '' (A ∩ W)))

def eventually_connectedComponentIn_eq_off_finite_rays_ball : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (d : Fin n → E) {F : ℝ → E} {v : E} {K : Set E} {R : ℝ}
    (hF : HasDerivAt F v 0) (h0 : F 0 = 0) (hv : v ≠ 0)
    (hdir : ∀ i, NormedSpace.normalize v ≠ NormedSpace.normalize (d i))
    (hK : Convex ℝ K) (hR : 0 < R)
    (hmodel : ∀ᶠ t : ℝ in 𝓝[>] 0, F t ∈ K ∧ t • v ∈ K),
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      F t ∈ (closedRays d)ᶜ ∩ (K ∩ Metric.ball 0 R) ∧
      t • v ∈ (closedRays d)ᶜ ∩ (K ∩ Metric.ball 0 R) ∧
      connectedComponentIn ((closedRays d)ᶜ ∩ (K ∩ Metric.ball 0 R)) (F t) =
        connectedComponentIn ((closedRays d)ᶜ ∩ (K ∩ Metric.ball 0 R)) (t • v)

def positiveAngle_oangle_map_complex : Prop :=
  ∀
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (o : Orientation ℝ E (Fin 2)) (C : E ≃ₗᵢ[ℝ] ℂ)
    (hC : Orientation.map (Fin 2) C.toLinearEquiv o = Complex.orientation)
    {u v : E} (hu : u ≠ 0) (hv : v ≠ 0),
    positiveAngle (o.oangle u v) = arg (branchCoordinate (C u) (C v)) + Real.pi

def raySector_iff_oangle_map_complex_lt : Prop :=
  ∀
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (o : Orientation ℝ E (Fin 2)) (C : E ≃ₗᵢ[ℝ] ℂ)
    (hC : Orientation.map (Fin 2) C.toLinearEquiv o = Complex.orientation)
    {u v w : E} {r : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0),
    C v ∈ raySector r (C u) (C w) ↔
      ‖branchCoordinate (C u) (C v)‖ < r ∧
        positiveAngle (o.oangle u v) < positiveAngle (o.oangle u w)

def exists_oriented_complex_isometry : Prop :=
  ∀
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2)),
    ∃ C : E ≃ₗᵢ[ℝ] ℂ,
      Orientation.map (Fin 2) C.toLinearEquiv o = Complex.orientation

def eventually_raySector_mem_iff_positive_oangle : Prop :=
  ∀
    {F : ℝ → ℂ} {v u w : ℂ} {r : ℝ}
    (hF : HasDerivAt F v 0) (h0 : F 0 = 0) (hr : 0 < r)
    (hu : u ≠ 0) (hw : w ≠ 0) (hv : v ≠ 0)
    (hvu : ¬SameRay ℝ v u) (hvw : ¬SameRay ℝ v w),
    (∀ᶠ t : ℝ in 𝓝[>] 0, F t ∈ raySector r u w) ↔
      positiveAngle (Complex.orientation.oangle u v) <
        positiveAngle (Complex.orientation.oangle u w)

def exists_original_tangent_sector_coordinates : Prop :=
  ∀
    {kind : SmoothManifolds.ModelKind} {M : Type*} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (c : ModelChart 2 kind M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source)
    (o : Orientation ℝ (TangentSpace S p) (Fin 2)),
    let K := (tangentStructure S).fiberCoordinates.equiv c hc p hp
    ∃ C : Euclidean 2 →L[ℝ] ℂ, Function.Injective C ∧
      ∀ u v : Euclidean 2, u ≠ 0 → v ≠ 0 →
        P202Specs.RegionalCornerTransport.positiveAngle
          (P202Specs.RegionalCornerTransport.tangentAngle g p o (K.symm u) (K.symm v)) =
            arg (branchCoordinate (C u) (C v)) + Real.pi

def exists_coordinateImage_germ_within : Prop :=
  ∀
    {n : ℕ} {kind : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
    (e d : ModelChart n kind M) (p : M)
    (hp : p ∈ e.source) (hpd : p ∈ d.source)
    (H : OpenPartialHomeomorph (Euclidean n) (Euclidean n))
    (hx : (e p).val ∈ H.source)
    (hrep : (fun q => H (e q).val) =ᶠ[𝓝 p] (fun q => (d q).val))
    (O : Set M) (hO : IsOpen O) (hpO : p ∈ O),
    ∃ W : Set M, IsOpen W ∧ p ∈ W ∧ W ⊆ O ∧ W ⊆ e.source ∩ d.source ∧
      (∀ q ∈ W, (e q).val ∈ H.source) ∧
      ∀ A : Set M, A ⊆ d.source → ∀ᶠ y : Euclidean n in 𝓝 (d p).val,
        (y ∈ (fun q => (d q).val) '' A ↔
          y ∈ H '' ((fun q => (e q).val) '' (A ∩ W)))

def exists_regionalDomain_atlas_germ : Prop :=
  ∀
    {kind : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 2 kind M) (K : FiberCoordinates S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (hpd : p ∈ (D.chart r).source)
    (O : Set M) (hO : IsOpen O) (hpO : p ∈ O),
    let L := ((K.equiv e he p hp).symm.trans
      (K.equiv (D.chart r) (D.chart_mem r) p hpd)).toContinuousLinearEquiv
    ∃ (H : OpenPartialHomeomorph (Euclidean 2) (Euclidean 2)) (W : Set M),
      (e p).val ∈ H.source ∧ H (e p).val = ((D.chart r) p).val ∧
      ContDiffAt ℝ (⊤ : ℕ∞) H (e p).val ∧
      ContDiffAt ℝ (⊤ : ℕ∞) H.symm ((D.chart r) p).val ∧
      HasFDerivAt H (L : Euclidean 2 →L[ℝ] Euclidean 2) (e p).val ∧
      HasFDerivAt H.symm (L.symm : Euclidean 2 →L[ℝ] Euclidean 2)
        ((D.chart r) p).val ∧
      ((fun q => H (e q).val) =ᶠ[𝓝 p] (fun q => ((D.chart r) q).val)) ∧
      ((fun q => H.symm ((D.chart r) q).val) =ᶠ[𝓝 p] (fun q => (e q).val)) ∧
      IsOpen W ∧ p ∈ W ∧ W ⊆ O ∧ W ⊆ e.source ∩ (D.chart r).source ∧
      (∀ q ∈ W, (e q).val ∈ H.source) ∧
      (∀ᶠ y : Euclidean 2 in 𝓝 ((D.chart r) p).val,
        (toPlane y ∈ (D.region r).domain ↔
          y ∈ H '' ((fun q => (e q).val) '' (regionInterior D r ∩ W)))) ∧
      (∀ v : Plane, ∀ᶠ t : ℝ in 𝓝[>] 0,
        (coordinates (D.chart r) p + t • v ∈ (D.region r).domain ↔
          toPlane.symm (coordinates (D.chart r) p + t • v) ∈
            H '' ((fun q => (e q).val) '' (regionInterior D r ∩ W))))

def eventually_tangent_ray_in_model : Prop :=
  ∀
    {kind : SmoothManifolds.ModelKind} (p : ModelSpace 2 kind)
    {F : ℝ → Plane} {v : Plane} (hF : HasDerivAt F v 0) (h0 : F 0 = 0)
    (hmodel : ∀ᶠ t : ℝ in 𝓝[>] 0,
      toPlane.symm (toPlane p.val + F t) ∈ modelSet 2 kind),
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      toPlane.symm (toPlane p.val + t • v) ∈ modelSet 2 kind

def graphStar_centered_coordinates_image : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {G : EmbeddedGraph S} {p : M} (g : GraphStar G p),
    (fun q => coordinates g.chart q - coordinates g.chart p) ''
      (g.neighborhood \ G.carrier) =
      (closedRays g.direction)ᶜ ∩ (centeredModel g ∩ Metric.ball 0 g.radius)

def graphStar_eventually_region_mem_iff : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {p : M} (D : RegionDecomposition S)
    (g : GraphStar D.graph p) (q r : ℝ → M) (v : Plane)
    (hF : HasDerivAt (fun t => coordinates g.chart (q t) - coordinates g.chart p) v 0)
    (h0 : coordinates g.chart (q 0) = coordinates g.chart p)
    (hv : v ≠ 0) (hdir : ∀ i, NormedSpace.normalize v ≠ g.direction i)
    (hqs : ∀ᶠ t : ℝ in 𝓝[>] 0, q t ∈ g.chart.source)
    (hrs : ∀ᶠ t : ℝ in 𝓝[>] 0, r t ∈ g.chart.source)
    (hray : ∀ᶠ t : ℝ in 𝓝[>] 0,
      coordinates g.chart (r t) = coordinates g.chart p + t • v),
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      q t ∈ g.neighborhood \ D.graph.carrier ∧
      r t ∈ g.neighborhood \ D.graph.carrier ∧
      ∀ j : Fin D.regionCount,
        (q t ∈ componentSet D.graph.carrierᶜ (D.component j) ↔
          r t ∈ componentSet D.graph.carrierᶜ (D.component j))

def eventually_planarRegion_domain_iff_derivative_ray : Prop :=
  ∀
    (R : PlanarRegion) (s : Fin R.boundaryCount → ℝ)
    (hs : IsInducedBoundaryOrientation R s)
    (i : Fin R.boundaryCount) (A : ArcPresentation (R.curve i)) (j : Fin A.count)
    {F : ℝ → Plane} {v : Plane} (hF : HasDerivAt F v 0) (hF0 : F 0 = A.arc j 1)
    (hv : v ≠ 0)
    (hvo : NormedSpace.normalize v ≠ NormedSpace.normalize (outgoingRay A (s i) j))
    (hvi : NormedSpace.normalize v ≠ NormedSpace.normalize (incomingRay A (s i) j)),
    ∀ᶠ t : ℝ in 𝓝[>] 0, (F t ∈ R.domain ↔ A.arc j 1 + t • v ∈ R.domain)

def occupiedSectorAngle_curved_test : Prop :=
  ∀
    {M : Type*} [TopologicalSpace M]
    {S : SmoothManifolds.AtlasData.SmoothManifold 2 .euclidean M}
    (g : P202.MetricData.RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : SmoothManifolds.ModelData.ModelChart 2 .euclidean M)
    (hc : c ∈ S.smoothStructure.val)
    (R : PlanarRegion) (s : Fin R.boundaryCount → ℝ)
    (hs : IsInducedBoundaryOrientation R s)
    (i : Fin R.boundaryCount) (A : ArcPresentation (R.curve i)) (j : Fin A.count)
    (alpha : ℝ) (hocc : IsOccupiedSectorAngle g o c hc R i A (s i) j alpha)
    {F : ℝ → Plane} {v : Plane} (hF : HasDerivAt F v 0) (hF0 : F 0 = A.arc j 1)
    (hv : v ≠ 0)
    (hvo : NormedSpace.normalize v ≠ NormedSpace.normalize (outgoingRay A (s i) j))
    (hvi : NormedSpace.normalize v ≠ NormedSpace.normalize (incomingRay A (s i) j)),
    (∀ᶠ t : ℝ in 𝓝[>] 0, F t ∈ R.domain) ↔
      positiveMetricAngle g o c hc (A.arc j 1) (outgoingRay A (s i) j) v < alpha

def regionalDomain_changed_chart_ray_transport : Prop :=
  ∀
    {kind : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 2 kind M) (K : FiberCoordinates S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (hpd : p ∈ (D.chart r).source)
    (s : Fin (D.region r).boundaryCount → ℝ)
    (hs : IsInducedBoundaryOrientation (D.region r) s)
    (i : Fin (D.region r).boundaryCount)
    (A : ArcPresentation ((D.region r).curve i)) (j : Fin A.count)
    (hj : A.arc j 1 = coordinates (D.chart r) p),
    let L := ((K.equiv e he p hp).symm.trans
      (K.equiv (D.chart r) (D.chart_mem r) p hpd)).toContinuousLinearEquiv
    ∀ (u : Euclidean 2), u ≠ 0 →
      NormedSpace.normalize (toPlane (L u)) ≠ NormedSpace.normalize (outgoingRay A (s i) j) →
      NormedSpace.normalize (toPlane (L u)) ≠ NormedSpace.normalize (incomingRay A (s i) j) →
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        (((e p).val + t • u ∈
            (fun q => (e q).val) '' (regionInterior D r ∩ e.source)) ↔
          coordinates (D.chart r) p + t • toPlane (L u) ∈ (D.region r).domain)

def regionalChartGeometry_occupiedSectorCurve_transport : Prop :=
  ∀
    {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (G : RegionalChartGeometry g D r) (p : G.neighborhood)
    (o : Orientation ℝ (TangentSpace S p.val) (Fin 2))
    (A : ∀ i, ArcPresentation ((D.region r).curve i))
    (s : Fin (D.region r).boundaryCount → ℝ)
    (hs : IsInducedBoundaryOrientation (D.region r) s)
    (i : Fin (D.region r).boundaryCount) (j : Fin (A i).count)
    (hj : (A i).arc j 1 = coordinates (D.chart r) p.val),
    let K := (tangentStructure S).fiberCoordinates.equiv
      (D.chart r) (D.chart_mem r) p.val (G.source_subset p.property)
    let V := fun v : Plane => K.symm (EuclideanSpace.equiv (Fin 2) ℝ v)
    let alpha := P202Specs.LocalGaussBonnet.interiorAngle G.metric G.orientation
      G.ambientChart G.ambientChart_mem (A i) (s i) j
    ∃ reversed : Bool, 0 < alpha ∧ alpha < 2 * Real.pi ∧
      ∀ {F : ℝ → Plane} {v : Plane}, HasDerivAt F v 0 → F 0 = (A i).arc j 1 →
        v ≠ 0 →
        NormedSpace.normalize v ≠ NormedSpace.normalize (outgoingRay (A i) (s i) j) →
        NormedSpace.normalize v ≠ NormedSpace.normalize (incomingRay (A i) (s i) j) →
        ((∀ᶠ t : ℝ in 𝓝[>] 0, F t ∈ (D.region r).domain) ↔
          (if reversed then positiveAngle (tangentAngle g p.val o (V v) (V (outgoingRay (A i) (s i) j)))
           else positiveAngle (tangentAngle g p.val o (V (outgoingRay (A i) (s i) j)) (V v))) < alpha)

def regionalChartGeometry_changed_chart_occupiedSectorAngle_transport : Prop :=
  ∀
    {kind : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    (D : RegionDecomposition S) (r : Fin D.regionCount)
    (G : RegionalChartGeometry g D r) (p : G.neighborhood)
    (o : Orientation ℝ (TangentSpace S p.val) (Fin 2))
    (A : ∀ i, ArcPresentation ((D.region r).curve i))
    (s : Fin (D.region r).boundaryCount → ℝ)
    (hs : IsInducedBoundaryOrientation (D.region r) s)
    (i : Fin (D.region r).boundaryCount) (j : Fin (A i).count)
    (hj : (A i).arc j 1 = coordinates (D.chart r) p.val)
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (hp : p.val ∈ e.source),
    let Ke := (tangentStructure S).fiberCoordinates.equiv e he p.val hp
    let Kd := (tangentStructure S).fiberCoordinates.equiv
      (D.chart r) (D.chart_mem r) p.val (G.source_subset p.property)
    let L := (Ke.symm.trans Kd).toContinuousLinearEquiv
    let alpha := P202Specs.LocalGaussBonnet.interiorAngle G.metric G.orientation
      G.ambientChart G.ambientChart_mem (A i) (s i) j
    ∃ reversed : Bool, 0 < alpha ∧ alpha < 2 * Real.pi ∧
      ∀ (u : Euclidean 2), u ≠ 0 →
        NormedSpace.normalize (toPlane (L u)) ≠
          NormedSpace.normalize (outgoingRay (A i) (s i) j) →
        NormedSpace.normalize (toPlane (L u)) ≠
          NormedSpace.normalize (incomingRay (A i) (s i) j) →
        ((∀ᶠ t : ℝ in 𝓝[>] 0, (e p.val).val + t • u ∈
            (fun q => (e q).val) '' (regionInterior D r ∩ e.source)) ↔
          (if reversed then positiveAngle (tangentAngle g p.val o
            (Ke.symm u)
            (Kd.symm (EuclideanSpace.equiv (Fin 2) ℝ (outgoingRay (A i) (s i) j))))
          else positiveAngle (tangentAngle g p.val o
            (Kd.symm (EuclideanSpace.equiv (Fin 2) ℝ (outgoingRay (A i) (s i) j)))
            (Ke.symm u))) < alpha)

end Expected
end P202Specs.RegionalCornerTransport
