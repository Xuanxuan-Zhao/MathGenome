import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.OrientedEuclideanDictionary

/-! Metric volume and unsigned tangent densities, d04:14:metric-density.
The fallback in `metricVolume` merely makes the definition total away from the
manifold hypotheses. Theorems establish the actual dimension and eliminate it.
Continuity of an intrinsic top field is expressed by its chart coefficients. -/
noncomputable section
open Set
open scoped ContDiff
namespace Specs.D04.C14.MetricTopFormsAndDensities
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
namespace Model
abbrev TangentTopField (r : ℕ∞ω) (k : ℕ) {n : ℕ} (M : Set (E n)) :=
  ∀ x : M, Covector (tangentSpace r k M x) k

def metricVolume {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o : TangentOrientationField r k M) : TangentTopField r k M := fun x =>
  if h : Module.finrank ℝ (tangentSpace r k M x) = k then
    letI : Fact (Module.finrank ℝ (tangentSpace r k M x) = k) := ⟨h⟩
    metricTopForm (o x x.property)
  else 0

/-- The density is defined intrinsically on each tangent tuple, with no orientation. -/
def tangentDensity {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (x : M) (v : Fin k → tangentSpace r k M x) : ℝ := gramDensity v

def chartDensity {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (u : E k) : ℝ :=
  gramDensity (fun i => chartDifferential c u (standardBasis k i))

/-- Pullback through the actual differential with values in the canonical tangent space. -/
def tangentPullback {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (η : TangentTopField r k M) (c : EmbeddedChart r k n M)
    (u : E k) (hu : u ∈ c.source) : Covector (E k) k :=
  (η ⟨c.toFun u, (c.map_source hu).1⟩).compLinearMap (tangentChartMap c u hu)

def zeroMetricVolume {r : ℕ∞ω} {n : ℕ} {M : Set (E n)}
    (o : ZeroManifoldOrientation M) : TangentTopField r 0 M :=
  fun x => scalarCovector (o x).val
end Model
open Model

abbrev TangentTopFieldType := ℕ∞ω → ℕ → {n : ℕ} → Set (E n) → Type
def TangentTopFieldValue : TangentTopFieldType := @Model.TangentTopField
abbrev metricVolumeType := {r : ℕ∞ω} → {k n : ℕ} → {M : Set (E n)} →
  TangentOrientationField r k M → TangentTopField r k M
def metricVolumeValue : metricVolumeType := @Model.metricVolume
abbrev tangentDensityType := {r : ℕ∞ω} → {k n : ℕ} → {M : Set (E n)} →
  (x : M) → (Fin k → tangentSpace r k M x) → ℝ
def tangentDensityValue : tangentDensityType := @Model.tangentDensity
abbrev chartDensityType := {r : ℕ∞ω} → {k n : ℕ} → {M : Set (E n)} →
  EmbeddedChart r k n M → E k → ℝ
def chartDensityValue : chartDensityType := @Model.chartDensity
abbrev tangentPullbackType := {r : ℕ∞ω} → {k n : ℕ} → {M : Set (E n)} →
  TangentTopField r k M → (c : EmbeddedChart r k n M) → (u : E k) →
    u ∈ c.source → Covector (E k) k
def tangentPullbackValue : tangentPullbackType := @Model.tangentPullback
abbrev zeroMetricVolumeType := {r : ℕ∞ω} → {n : ℕ} → {M : Set (E n)} →
  ZeroManifoldOrientation M → TangentTopField r 0 M
def zeroMetricVolumeValue : zeroMetricVolumeType := @Model.zeroMetricVolume

def metricVolume_normalizedType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r k M →
    ∀ (o : TangentOrientationField r k M) (x : M)
      (b : OrthonormalBasis (Fin k) ℝ (tangentSpace r k M x)),
      b.toBasis.orientation = o x x.property → metricVolume o x b = 1

def metricVolume_uniqueType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r k M → 0 < k →
    ∀ (o : TangentOrientationField r k M) (η : TangentTopField r k M),
      (∀ (x : M) (b : OrthonormalBasis (Fin k) ℝ (tangentSpace r k M x)),
        b.toBasis.orientation = o x x.property → η x b = 1) → η = metricVolume o

def metricVolume_pullbackType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r k M → 0 < k →
    ∀ (o : TangentOrientationField r k M) (c : EmbeddedChart r k n M)
      (u : E k) (hu : u ∈ c.source),
    tangentPullback (metricVolume o) c u hu =
      (chartSign o c u hu * chartDensity c u) • omega k

def metricVolume_positive_chartType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r k M → 0 < k →
    ∀ (o : TangentOrientationField r k M) (c : EmbeddedChart r k n M)
      (u : E k) (hu : u ∈ c.source), chartSign o c u hu = 1 →
    tangentPullback (metricVolume o) c u hu = chartDensity c u • omega k

def metricVolume_reverseType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (o : TangentOrientationField r k M),
    metricVolume (fun x hx => -o x hx) = -metricVolume o

/-- Both orientations, and indeed any choices of orientation, give this same density. -/
def metricVolume_abs_densityType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r k M →
    ∀ (o : TangentOrientationField r k M) (x : M) (v : Fin k → tangentSpace r k M x),
      |metricVolume o x v| = tangentDensity x v

def density_chartType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c : EmbeddedChart r k n M)
    (u : E k) (hu : u ∈ c.source),
    tangentDensity ⟨c.toFun u, (c.map_source hu).1⟩
      (fun i => tangentChartMap c u hu (standardBasis k i)) = chartDensity c u

/-- Absolute determinant transformation on arbitrary tangent frames, even dependent ones. -/
def density_linear_changeType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (x : M)
    (F : E k →ₗ[ℝ] tangentSpace r k M x) (A : E k →ₗ[ℝ] E k),
    tangentDensity x (fun i => F (A (standardBasis k i))) =
      |LinearMap.det A| * tangentDensity x (fun i => F (standardBasis k i))

def chartDensity_matrixType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c : EmbeddedChart r k n M) (u : E k),
    chartDensity c u = Real.sqrt (Matrix.det
      ((matrixOfLinearMap (chartDifferential c u).toLinearMap).transpose *
        matrixOfLinearMap (chartDifferential c u).toLinearMap))

def chartDensity_positiveType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c : EmbeddedChart r k n M),
    ManifoldRegularity r → ∀ u ∈ c.source, 0 < chartDensity c u

def chartDensity_reparametrizeType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c d : EmbeddedChart r k n M),
    ManifoldRegularity r → ∀ (h : E k → E k) (hm : MapsTo h c.source d.source),
      EqOn c.toFun (d.toFun ∘ h) c.source →
      ∀ u ∈ c.source, ∀ A : E k →L[ℝ] E k, HasFDerivWithinAt h A c.source u →
        chartDensity c u = |LinearMap.det A.toLinearMap| * chartDensity d (h u)

def chartDensity_transitionType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c d : EmbeddedChart r k n M),
    ManifoldRegularity r → k ≤ n → ∀ u ∈ chartOverlap c d,
    chartDensity c u =
      |LinearMap.det (fderivWithin ℝ (chartTransition c d) (chartOverlap c d) u).toLinearMap| *
        chartDensity d (chartTransition c d u)

def chartDensity_continuousType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c : EmbeddedChart r k n M),
    ManifoldRegularity r → ContinuousOn (chartDensity c) c.source

def metricVolume_continuousType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (o : PositiveManifoldOrientation r k M)
    (c : EmbeddedChart r k n M),
    Continuous (fun u : c.source =>
      tangentPullback (metricVolume o.atPoint) c u u.property (standardBasis k))

/-- These algebraic statements apply directly to the derivative of every chart. -/
def gram_speedType : Prop := ∀ {n : ℕ} (A : E 1 →L[ℝ] E n),
  gramDensity (fun i => A (standardBasis 1 i)) = ‖A (standardBasis 1 0)‖
def gram_crossType : Prop := ∀ (A : E 2 →L[ℝ] E 3),
  gramDensity (fun i => A (standardBasis 2 i)) =
    ‖euclideanCross (A (standardBasis 2 0)) (A (standardBasis 2 1))‖
def gram_full_dimensionType : Prop := ∀ {n : ℕ} (A : E n →L[ℝ] E n),
  gramDensity (fun i => A (standardBasis n i)) = |Matrix.det (matrixOfLinearMap A.toLinearMap)|
def density_zeroType : Prop :=
  ∀ {r : ℕ∞ω} {n : ℕ} {M : Set (E n)} (x : M) (v : Fin 0 → tangentSpace r 0 M x),
    tangentDensity x v = 1
def metricVolume_zeroType : Prop :=
  ∀ {r : ℕ∞ω} {n : ℕ} {M : Set (E n)} (o : ZeroManifoldOrientation M)
    (x : M) (v : Fin 0 → tangentSpace r 0 M x), zeroMetricVolume o x v = (o x).val

def zeroMetricVolume_pullbackType : Prop :=
  ∀ {r : ℕ∞ω} {n : ℕ} {M : Set (E n)} (o : ZeroManifoldOrientation M)
    (c : EmbeddedChart r 0 n M) (u : E 0) (hu : u ∈ c.source),
    tangentPullback (zeroMetricVolume o) c u hu =
      (o ⟨c.toFun u, (c.map_source hu).1⟩).val • omega 0
end Specs.D04.C14.MetricTopFormsAndDensities
