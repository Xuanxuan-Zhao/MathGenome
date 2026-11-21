import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SmoothMetrics
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.Densities
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Topology
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.BoundaryRegularLevels
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-! Riemannian densities use the absolute dual of the actual determinant line.
The cotangent realization below uses exactly the tangent realization fixed by
SmoothMetrics. No metric, orientation, measure or integral certificate is added
to the hypotheses. This file is independent of the candidate implementation. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Topology CompactlySupported ENNReal

namespace P202.VolumeData
open SmoothManifolds hiding SmoothManifold ModelChart TangentSpace Euclidean modelSet ModelSpace sectionSupport
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.BundleOperationsData SmoothManifolds.MetricVolumeData
  SmoothManifolds.ExteriorData SmoothManifolds.OrientationData
  SmoothManifolds.DensityIntegrationData P202.MetricData
universe u

/-- Choose only the dual of the already fixed tangent realization. -/
def cotangentBundle {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) : CotangentBundle S where
  tangent := tangentStructure S
  realization := tangentRealization S
  dual := Classical.choice (BundleOperations.exists_dual (tangentRealization S).space.bundle)

/-- Identity adapter: the metric and every bilinear form remain unchanged. -/
def libraryMetric {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) : Metric (cotangentBundle S) := g

/-- The Gram matrix in the actual coordinate basis of the tangent fiber. -/
def gramMatrix {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j => P202.MetricData.pairing g p.val
    ((K.equiv c hc p.val p.property).symm ((Pi.basisFun ℝ (Fin n)) i))
    ((K.equiv c hc p.val p.property).symm ((Pi.basisFun ℝ (Fin n)) j)))

def density {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) : DensityField S :=
  MetricVolumeResults.metricDensity (libraryMetric g)

def topFormBundle {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) : FormBundle (cotangentBundle S) n :=
  Classical.choice (ExteriorAlgebraResults.exists_formBundle (cotangentBundle S) n)

def volumeForm {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (o : Orientation S) :
    Form (topFormBundle S) :=
  (MetricVolumeResults.volume_exists_unique S (cotangentBundle S)
    (topFormBundle S) (libraryMetric g) o).choose

def densityIntegral {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) : CompactDensity S → ℝ :=
  (DensityIntegralResults.integral_exists_unique S).choose

/-- Multiplication by a compactly supported continuous scalar function. -/
def compactMetricDensity {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (f : C_c(M, ℝ)) :
    CompactDensity S where
  field := fun p => f p • density g p
  continuous := by
    intro K c hc
    have hρ := DensityIntegrationResults.smooth_density_continuous (density g)
      (MetricVolumeResults.metricDensity_smooth (libraryMetric g)) K c hc
    exact ((f.continuous.comp continuous_subtype_val).mul hρ).congr
      (fun p => (map_smul (densityCoefficient K c hc p) _ _).symm)
  compact_support := f.hasCompactSupport.of_isClosed_subset isClosed_closure
    (fun p hp => (DensityIntegralResults.support_weight_subset (fun p => f p) (density g) hp).1)

def integral {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (f : C_c(M, ℝ)) : ℝ :=
  densityIntegral S (compactMetricDensity g f)

/-- Coordinate integrands are zero outside the chart target and the actual
model. Thus the formula also covers half-space charts at true boundary points. -/
def chartIntegrand {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (f : M → ℝ)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) :
    Euclidean n → ℝ :=
  LocalIntegrationData.extendModel (fun x => if hx : x ∈ c.target then
    f (c.symm x) * Real.sqrt (gramMatrix g K c hc ⟨c.symm x, c.map_target hx⟩).det else 0)

def chartLIntegrand {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (f : M → ℝ≥0∞)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (x : Euclidean n) : ℝ≥0∞ :=
  if hx : x ∈ modelSet n a then
    if hy : (⟨x, hx⟩ : ModelSpace n a) ∈ c.target then
      f (c.symm ⟨x, hx⟩) *
        ENNReal.ofReal (Real.sqrt (gramMatrix g K c hc
          ⟨c.symm ⟨x, hx⟩, c.map_target hy⟩).det)
    else 0
  else 0

end P202.VolumeData

namespace P202Specs.Geometry.RiemannianVolume
open SmoothManifolds hiding SmoothManifold ModelChart TangentSpace Euclidean modelSet ModelSpace sectionSupport
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.BundleOperationsData SmoothManifolds.MetricVolumeData
  SmoothManifolds.ExteriorData SmoothManifolds.OrientationData
  SmoothManifolds.DensityIntegrationData P202.MetricData P202.VolumeData
universe u

/-- The adapter is an equality of actual tangent-fiber bilinear forms. -/
def metric_bridgeType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (p : M),
    metricForm (libraryMetric g) p = P202.MetricData.pairing g p

def densityType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} → RiemannianMetric S → DensityField S

def densityValue : densityType := @density

def density_propertiesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S),
    IsMetricDensity (libraryMetric g) (density g) ∧ IsSmoothDensity (density g) ∧
      IsContinuousDensity (density g) ∧ IsPositiveDensity (density g) ∧
      (∀ p, density g p ≠ 0)

def density_uniqueType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (ρ : DensityField S),
    IsMetricDensity (libraryMetric g) ρ → ρ = density g

def density_coordinatesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source),
    densityCoefficient K c hc p (density g p.val) = Real.sqrt (gramMatrix g K c hc p).det ∧
      0 < Real.sqrt (gramMatrix g K c hc p).det

def density_overlapType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (K : FiberCoordinates S)
    (c d : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : ↥(c.source ∩ d.source)),
    densityCoefficient K d hd ⟨p.val, p.property.2⟩ (density g p.val) =
      |transitionDeterminant K d c hd hc ⟨p.val, p.property.2, p.property.1⟩| *
        densityCoefficient K c hc ⟨p.val, p.property.1⟩ (density g p.val)

def density_zero_dimensionType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 a M} (g : RiemannianMetric S) (p : M),
    (density g p).val ((exteriorPower.zeroEquiv ℝ (TangentSpace S p)).symm 1) = 1

def volumeFormType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} →
  RiemannianMetric S → Orientation S → Form (topFormBundle S)

def volumeFormValue : volumeFormType := @volumeForm

def volumeForm_propertiesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (o : Orientation S),
    IsMetricVolume (libraryMetric g) o (volumeForm g o) ∧
      absoluteTopForm (volumeForm g o).field = density g ∧
      ∀ (p : M) (v : DeterminantLine S p), IsPositive (o.val p) v →
        0 < OrientationData.pairing p ((volumeForm g o).field p) v

def volumeForm_coordinatesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (o : Orientation S)
    (s : SignedCharts S), RepresentsSignedCharts o.val s →
    ∀ (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source), (volumeForm g o).field p.val =
      (signValue (s.sign c hc p) * Real.sqrt (gramMatrix g K c hc p).det) •
        coordinateTopForm K c hc p

def densityIntegralType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → (S : SmoothManifold n a M) → CompactDensity S → ℝ

def densityIntegralValue : densityIntegralType := @densityIntegral

def densityIntegral_propertiesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M), IsDensityIntegral (densityIntegral S) ∧
      ∀ I : CompactDensity S → ℝ, IsDensityIntegral I → I = densityIntegral S

def integralType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} →
  RiemannianMetric S → C_c(M, ℝ) → ℝ

def integralValue : integralType := @integral

def integral_chartType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (f : C_c(M, ℝ))
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val),
    tsupport f ⊆ c.source → integral g f =
      DensityIntegrationData.coordinateIntegral K c hc (fun p => f p • density g p)

/-- The genuine intrinsic boundary, in its natural face atlas, receives the
pullback metric by its injective tangent differential. This includes an empty
boundary and n = 0, without orientability or compactness assumptions. -/
def boundaryDensity_existsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (g : RiemannianMetric S),
    ∃ (B : SmoothManifold (n - 1) .euclidean (BoundaryData.intrinsicBoundary S))
      (hB : BoundaryRegularLevelData.IsNaturalBoundaryStructure S B)
      (gB : RiemannianMetric B) (dS : DensityField B),
      (∀ p v w, P202.MetricData.pairing gB p v w =
        P202.MetricData.pairing g p.val
          (SmoothManifolds.differential B S Subtype.val hB.1 p v)
          (SmoothManifolds.differential B S Subtype.val hB.1 p w)) ∧
      dS = density gB ∧ IsSmoothDensity dS ∧ IsPositiveDensity dS

/-- The induced Borel measure is uniquely characterized by the *constructed*
compact-density integral. Regularity includes finiteness on every compact set. -/
def measure_representation_existsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S),
    letI : MeasurableSpace M := borel M
    ∃! μ : MeasureTheory.Measure M, μ.Regular ∧
      (∀ C : Set M, IsCompact C → μ C < ⊤) ∧
      ∀ f : C_c(M, ℝ), (∫ p, f p ∂μ) = integral g f

def chart_weight_formulaType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (f : M → ℝ)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val),
    coordinateDensity K c hc (fun p => f p • density g p) = chartIntegrand g f K c hc

def integral_chart_sqrtType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (f : C_c(M, ℝ))
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val),
    tsupport f ⊆ c.source → integral g f = ∫ x, chartIntegrand g f K c hc x

/-- No continuity or compact-support hypothesis on the scalar integrand.
The closed support lies in the overlap; this is the source's support convention. -/
def localIntegral_overlapType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (f : M → ℝ)
    (K J : FiberCoordinates S) (c d : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val), tsupport f ⊆ c.source → tsupport f ⊆ d.source →
    (∫ x, chartIntegrand g f K c hc x) = ∫ x, chartIntegrand g f J d hd x

/-- Full measurable localization: the measure constructed
from the density integral must have the chart formula for every nonnegative
measurable integrand and every integrable real integrand supported in the chart.
The measure is characterized by the intrinsic compact-density integral. -/
def measure_chart_existsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S),
    letI : MeasurableSpace M := borel M
    ∃ μ : MeasureTheory.Measure M, μ.Regular ∧
      (∀ C : Set M, IsCompact C → μ C < ⊤) ∧
      (∀ f : C_c(M, ℝ), (∫ p, f p ∂μ) = integral g f) ∧
      ∀ (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val),
        (∀ f : M → ℝ≥0∞, Measurable f → Function.support f ⊆ c.source →
          (∫⁻ p, f p ∂μ) = ∫⁻ x, chartLIntegrand g f K c hc x) ∧
        (∀ f : M → ℝ, MeasureTheory.Integrable f μ → Function.support f ⊆ c.source →
          (∫ p, f p ∂μ) = ∫ x, chartIntegrand g f K c hc x)

/-- Nonnegative chart integrals agree on overlaps without compact support. -/
def localLIntegral_overlapType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S),
    letI : MeasurableSpace M := borel M
    ∀ (f : M → ℝ≥0∞), Measurable f →
    ∀ (K J : FiberCoordinates S) (c d : ModelChart n a M)
      (hc : c ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val),
    Function.support f ⊆ c.source → Function.support f ⊆ d.source →
      (∫⁻ x, chartLIntegrand g f K c hc x) = ∫⁻ x, chartLIntegrand g f J d hd x

/-- The overlap multiplier is the absolute determinant of the actual
coordinate Jacobian, including ambient smooth extensions at a true boundary. -/
def density_overlap_jacobianType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (K : FiberCoordinates S)
    (c d : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : ↥(c.source ∩ d.source))
    (U : Set (Euclidean n)) (F : Euclidean n → Euclidean n),
    IsOpen U → (d p.val).val ∈ U → ContDiffOn ℝ (⊤ : ℕ∞) F U →
    (fun q => F (d q).val) =ᶠ[𝓝 p.val] (fun q => (c q).val) →
    densityCoefficient K d hd ⟨p.val, p.property.2⟩ (density g p.val) =
      |(fderiv ℝ F (d p.val).val).toLinearMap.det| *
        densityCoefficient K c hc ⟨p.val, p.property.1⟩ (density g p.val)

end P202Specs.Geometry.RiemannianVolume
