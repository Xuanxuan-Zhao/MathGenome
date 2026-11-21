import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PolarVolumeDensity
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CutLocusNull
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ModelPolarDomains
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ConstantCurvaturePolar
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The ball integration identities in paper.tex 4471–4480, including the
one-sided endpoint convention at 4490–4494. No Ricci hypothesis is used.

Volumes are values of the genuine Borel Riemannian measure, constructed
from compactly supported density integration upstream. The nonnegative
integral formulation of the first identity avoids any integrability convention
for an unbounded density. Finiteness is a separate conclusion.

`modelVolume g p` is V for the specified actual model realization and center,
not a definition by a comparison integral. The three model statements quantify
all the original Euclidean, round-spherical and induced hyperboloid realizations.
Their curvature parameters are respectively 0, 1/a² and -1/a², which cover all
real curvatures. Thus no classification theorem or additional polar certificate
is imposed on the models. The spherical statement includes r = πa.
-/
set_option autoImplicit false
noncomputable section
open scoped ENNReal Topology

namespace P202.PolarIntegrationData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  P202.MetricData P202.CompleteExponentialData
open Set MeasureTheory
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Open ball for the original Riemannian length distance. -/
def metricBall (g : RiemannianMetric S) (p : M) (r : ℝ) : Set M :=
  {q | lengthDistance g p q < r}

/-- Actual Riemannian ball volume, with extended nonnegative values. -/
def ballVolume (g : RiemannianMetric S) (p : M) (r : ℝ) : ℝ≥0∞ :=
  P202.CutNullData.volume g (metricBall g p r)

/-- V for a specified geometric model and center, defined by its metric ball. -/
def modelVolume (g : RiemannianMetric S) (p : M) (r : ℝ) : ℝ≥0∞ :=
  ballVolume g p r

/-- Standard area of the Euclidean unit (n-1)-sphere, with cone normalization. -/
def omega (n : ℕ) : ℝ≥0∞ :=
  (volume : Measure (P202.SpaceFormData.E n)).toSphere univ

/-- The upper comparison radius; infinity is retained for k ≤ 0. -/
def rho (k : ℝ) : ℝ≥0∞ :=
  if 0 < k then ENNReal.ofReal (Real.pi / Real.sqrt k) else ⊤

end P202.PolarIntegrationData

namespace P202Specs.Geometry.PolarVolumeIntegration
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MaximalFlowData P202.MetricData P202.ConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CompletenessData
  P202.CurvatureData P202.CutTimeData P202.PolarVolumeData
  P202.PolarIntegrationData P202.SpaceFormData P202.ModelPolarData
  P202.ConstantCurvaturePolarData
open Set Filter MeasureTheory
universe u

/-- Full polar integration formula on every complete connected manifold,
for arbitrary correct auxiliary connection and maximal exponential family. -/
def ball_integralType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S), 2 ≤ n →
    LengthMetricComplete g → ∀ C : Connection (tangentBundle S), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ F : CurveFamily (Phase S), IsMaximalFamily S C F →
    ∀ (p : M) (r : ℝ), 0 < r →
      ballVolume g p r =
        ∫⁻ t in Ioo (0 : ℝ) r, ∫⁻ v, ENNReal.ofReal (truncatedDensity g F p (t,v))
          ∂sphereMeasure g p

/-- These actual open balls have finite volume; no curvature bound is needed. -/
def ball_volume_finiteType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S),
    LengthMetricComplete g → ∀ (p : M) (r : ℝ), ballVolume g p r < ⊤

/-- Increasing union of open balls gives the value at every positive finite
endpoint, in particular at the spherical comparison radius. -/
def ball_volume_left_limitType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (p : M) (r : ℝ), 0 < r →
      Tendsto (ballVolume g p) (𝓝[<] r) (𝓝 (ballVolume g p r))

/-- V_0^n for actual complete simply connected Euclidean models. -/
def euclidean_volumeType : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ G : EuclideanModel n, G.Conclusion →
    ∀ (p : E n) (r : ℝ), 0 < r →
      modelVolume G.metric p r =
        omega n * ENNReal.ofReal (∫ t in (0 : ℝ)..r, s 0 t ^ (n-1))

/-- V_(1/a²)^n, including its actual value at r = πa and its one-sided limit.
There is no assumption of the desired normal-domain or volume identity. -/
def spherical_volumeType : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ a : ℝ, 0 < a →
    ∀ (A : EuclideanModel (n+1)) (B : SphericalModel n a A), B.Conclusion →
    ∀ (p : Sphere n a) (r : ℝ), 0 < r → r ≤ Real.pi * a →
      modelVolume B.metric p r =
        omega n * ENNReal.ofReal (∫ t in (0 : ℝ)..r, s ((a^2)⁻¹) t ^ (n-1))

/-- V_(-1/a²)^n for the genuine induced complete hyperboloid model.
Completeness is the original geometric hypothesis, proved for the constructed
models upstream; the chart fixes their original smooth structure. -/
def hyperbolic_volumeType : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ a : ℝ, 0 < a →
    ∀ (S : SmoothManifold n .euclidean (P202.HyperboloidData.Hyperboloid n a))
      (g : RiemannianMetric S) (C : Connection (tangentBundle S)),
    HasProjectionChart S → P202.HyperboloidData.IsInduced g → IsLeviCivita g C →
    LengthMetricComplete g →
    ∀ (p : P202.HyperboloidData.Hyperboloid n a) (r : ℝ), 0 < r →
      modelVolume g p r =
        omega n * ENNReal.ofReal (∫ t in (0 : ℝ)..r, s (-(a^2)⁻¹) t ^ (n-1))

/-- All three actual model-ball identities. The normalization omega is the
same standard Euclidean sphere area for every model and center. -/
def model_volumeType : Prop :=
  euclidean_volumeType ∧ spherical_volumeType ∧ hyperbolic_volumeType

end P202Specs.Geometry.PolarVolumeIntegration
