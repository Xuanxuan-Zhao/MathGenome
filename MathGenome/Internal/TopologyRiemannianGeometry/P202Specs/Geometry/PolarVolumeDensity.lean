import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.JacobiMatrix
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CutPolarDomain
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.RiemannianVolume
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Prod

/-! Polar volume density, paper.tex 4420–4447 and 4465–4477.

All differentials and densities below use the original intrinsic tangent
fibers. The definition of j uses the unsigned volume Jacobian of exp, so it
does not select a direction-dependent frame. The theorem identifies it with
*the signed determinant* of every actual normal Jacobi system in a parallel
orthonormal frame before the cut time. The round sphere measure is defined by
the usual cone construction from the metric Lebesgue measure on T_p M.
No curvature bound or orientation is part of these statements. -/
set_option autoImplicit false
noncomputable section
open scoped Topology ENNReal
open Module

namespace P202.PolarVolumeData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData SmoothManifolds.DensityIntegrationData
  P202.MetricData P202.ConnectionData P202.CurveConnectionData P202.GeodesicData
  P202.ExponentialData P202.ExponentialJacobiData P202.JacobiMatrixData
  P202.CutTimeData P202.CutPolarData
open Set MeasureTheory
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- A fixed topology on the actual metric unit tangent sphere. -/
instance directionTopologicalSpace (g : RiemannianMetric S) (p : M) :
    TopologicalSpace (UnitDirection g p) :=
  directionTopology g p (selectedCoordinates S p)

instance directionMeasurableSpace (g : RiemannianMetric S) (p : M) :
    MeasurableSpace (UnitDirection g p) := borel _

instance directionBorelSpace (g : RiemannianMetric S) (p : M) :
    BorelSpace (UnitDirection g p) := ⟨rfl⟩

/-- Coordinate basis of the original tangent fiber, with no metric assumption
on the auxiliary linear coordinates E. -/
def fiberBasis (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    Basis (Fin n) ℝ (TangentSpace S p) := (Pi.basisFun ℝ (Fin n)).map E.symm

def fiberVolume (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) : ℝ :=
  tupleEvaluation (P202.VolumeData.density g p) (fiberBasis p E)

/-- The metric volume Jacobian of the genuine exponential differential.
The denominator is the volume of the *same* source basis at p. -/
def exponentialJacobian (g : RiemannianMetric S) (F : CurveFamily (Phase S))
    (p : M) (w : TangentSpace S p)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) : ℝ :=
  tupleEvaluation (P202.VolumeData.density g (fiberExponential F p w))
    (fun i => fiberDifferential S F p w (fiberBasis p E i)) / fiberVolume g p E

/-- Canonical, frame-free polar density. The t^(n-1) factor is the Jacobian
of (t,v) ↦ tv relative to dt and the round sphere measure at p. -/
def radialDensity (g : RiemannianMetric S) (F : CurveFamily (Phase S)) (p : M)
    (tv : ℝ × UnitDirection g p) : ℝ :=
  tv.1 ^ (n - 1) * exponentialJacobian g F p (tv.1 • tv.2.val)
    (selectedCoordinates S p)

/-- Zero outside the open polar domain, including nonpositive radii and
finite cut endpoints. An infinite cut time is never replaced by a finite one. -/
def truncatedDensity (g : RiemannianMetric S) (F : CurveFamily (Phase S)) (p : M)
    (tv : ℝ × UnitDirection g p) : ℝ :=
  (polarDomain g F p).indicator (radialDensity g F p) tv

/-- Angular measure is n times the metric volume of the unit cone. This
coordinate formula defines the standard sphere measure induced by g_p;
the cone characterization and independence of E are theorem obligations. -/
def sphereMeasure (g : RiemannianMetric S) (p : M) : Measure (UnitDirection g p) :=
  let E := selectedCoordinates S p
  let unitBall : Set (Euclidean n) := {x | tangentNorm g p (E.symm x) < 1}
  let normalize : Euclidean n → Euclidean n :=
    fun x => (tangentNorm g p (E.symm x))⁻¹ • x
  (ENNReal.ofReal ((n : ℝ) * fiberVolume g p E)) •
    (Measure.map normalize (volume.restrict unitBall)).comap (fun v => E v.val)

def unitCone (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (B : Set (UnitDirection g p)) :
    Set (Euclidean n) :=
  {x | ∃ r ∈ Ioo (0 : ℝ) 1, ∃ v ∈ B, x = r • E v.val}

/-- Only genuine frame properties are data here: no determinant, Jacobian,
measurability, or asymptotic assertion is assumed. The coordinate inner product
is the standard dot product, since Euclidean r is implemented as Fin r → ℝ. -/
def IsOrthonormalNormalFrame {r : ℕ} (g : RiemannianMetric S)
    {C : Connection (tangentBundle S)} {R : P202.CurvatureData.CurvatureTensor S}
    {I : D13Unified.OpenTimeInterval} {q : ℝ → Phase S}
    (D : JacobiSystem S C R I q r) : Prop :=
  (∀ t ∈ I.carrier, ∀ x y,
    pairing g (q t).1 (D.frame t x) (D.frame t y) = ∑ i, x i * y i) ∧
  (∀ t ∈ I.carrier, ∀ w : TangentSpace S (q t).1,
    (∃ x, D.frame t x = w) ↔ pairing g (q t).1 w (q t).2 = 0)

end P202.PolarVolumeData

namespace P202Specs.Geometry.PolarVolumeDensity
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData P202.MetricData P202.ConnectionData
  P202.CurveConnectionData P202.LeviCivitaData P202.GeodesicData P202.CurvatureData
  P202.ExponentialData P202.ExponentialJacobiData P202.JacobiMatrixData
  P202.CompletenessData P202.CutTimeData P202.CutPolarData P202.PolarVolumeData
open Set Filter MeasureTheory
universe u

def radialDensityType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → (g : RiemannianMetric S) →
  CurveFamily (Phase S) → (p : M) → (ℝ × UnitDirection g p) → ℝ

def radialDensityValue : radialDensityType := @radialDensity

def truncatedDensityValue : radialDensityType := @truncatedDensity

def sphereMeasureType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → (g : RiemannianMetric S) →
  (p : M) → Measure (UnitDirection g p)

def sphereMeasureValue : sphereMeasureType := @sphereMeasure

/-- An arbitrary linear source basis computes the same metric Jacobian,
even without completeness or regularity of the exponential at that vector. -/
def jacobian_independenceType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M}
    (g : RiemannianMetric S) (F : CurveFamily (Phase S)) (p : M)
    (w : TangentSpace S p) (E E' : TangentSpace S p ≃ₗ[ℝ] Euclidean n),
    exponentialJacobian g F p w E = exponentialJacobian g F p w E'

/-- First-order initial data already imply the exact initial determinant
normalization, for any rank, including zero. -/
def system_normalizationType : Prop :=
  ∀ {n r : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S))
    (R : CurvatureTensor S) (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
    0 ∈ I.carrier → ∀ D : JacobiSystem S C R I q r,
      Tendsto (fun t => LinearMap.det (D.A t).toLinearMap / t ^ r)
        (𝓝[>] (0 : ℝ)) (𝓝 1)

/-- Signed determinant positivity before the actual cut time. This holds
also for nonorthonormal parallel systems and every rank. -/
def system_positiveType : Prop :=
  ∀ {n r : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S), 2 ≤ n →
    LengthMetricComplete g → ∀ C : Connection (tangentBundle S), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
      (p : M) (v : UnitDirection g p)
      (D : JacobiSystem S C R (F.interval ⟨p, v.val⟩) (F.curve ⟨p, v.val⟩) r)
      (t : ℝ), 0 < t → ENNReal.ofReal t < cutTime g F p v →
      0 < LinearMap.det (D.A t).toLinearMap

/-- The required parallel orthonormal systems exist; no auxiliary frame or
Jacobi solution is imposed as an extra hypothesis on the manifold. -/
def normal_frame_existsType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S), 2 ≤ n →
    LengthMetricComplete g → ∀ C : Connection (tangentBundle S), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ (p : M) (v : UnitDirection g p),
      ∃ D : JacobiSystem S C R (F.interval ⟨p, v.val⟩) (F.curve ⟨p, v.val⟩) (n-1),
        IsOrthonormalNormalFrame g D

/-- Change of parallel orthonormal frames is a single constant orthogonal
matrix, acting by conjugacy on A. Thus det A has no auxiliary frame choice. -/
def frame_compatibilityType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
    IsGeodesicOn S C I.carrier q → 0 ∈ I.carrier →
    ∀ D E : JacobiSystem S C R I q (n-1),
      IsOrthonormalNormalFrame g D → IsOrthonormalNormalFrame g E →
      ∃ Q : Euclidean (n-1) ≃ₗ[ℝ] Euclidean (n-1),
        (∀ x y, (∑ i, Q x i * Q y i) = ∑ i, x i * y i) ∧
        ∀ t ∈ I.carrier,
          (∀ x, E.frame t x = D.frame t (Q x)) ∧
          (∀ x, D.A t (Q x) = Q (E.A t x)) ∧
          LinearMap.det (D.A t).toLinearMap = LinearMap.det (E.A t).toLinearMap

/-- The positive *signed* Jacobi determinant equals the canonical polar
volume density for every actual orthonormal normal system. -/
def jacobi_densityType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S), 2 ≤ n →
    LengthMetricComplete g → ∀ C : Connection (tangentBundle S), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ (p : M) (v : UnitDirection g p)
      (D : JacobiSystem S C R (F.interval ⟨p, v.val⟩) (F.curve ⟨p, v.val⟩) (n-1)),
      IsOrthonormalNormalFrame g D →
      ∀ t : ℝ, 0 < t → ENNReal.ofReal t < cutTime g F p v →
        radialDensity g F p (t,v) = LinearMap.det (D.A t).toLinearMap ∧
          0 < radialDensity g F p (t,v)

/-- Round sphere measure, including its normalization and independence of
all auxiliary source coordinates. This is the metric cone characterization. -/
def sphere_measureType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S), 2 ≤ n →
    ∀ p : M,
      IsFiniteMeasure (sphereMeasure g p) ∧ sphereMeasure g p Set.univ ≠ 0 ∧
      ∀ (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (B : Set (UnitDirection g p)),
        MeasurableSet B →
        sphereMeasure g p B = ENNReal.ofReal ((n : ℝ) * fiberVolume g p E) *
          volume (unitCone g p E B)

/-- Local joint continuity is required before extending by zero across the
cut-time graph. It does not assert continuity at the cut endpoints. -/
def continuityType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S), 2 ≤ n →
    LengthMetricComplete g → ∀ C : Connection (tangentBundle S), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ p : M, ContinuousOn (radialDensity g F p) (polarDomain g F p)

/-- Source basis compatibility, initial normalization, local regularity,
and Borel measurability on the entire product after truncation. -/
def regularityType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S), 2 ≤ n →
    LengthMetricComplete g → ∀ C : Connection (tangentBundle S), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ p : M,
      (∀ v : UnitDirection g p,
        Tendsto (fun t => radialDensity g F p (t,v) / t ^ (n-1))
          (𝓝[>] (0 : ℝ)) (𝓝 1)) ∧
      ContinuousOn (radialDensity g F p) (polarDomain g F p) ∧
      Measurable (truncatedDensity g F p) ∧
      (∀ tv, 0 ≤ truncatedDensity g F p tv) ∧
      (∀ (w : TangentSpace S p) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n),
        exponentialJacobian g F p w E =
          exponentialJacobian g F p w (selectedCoordinates S p))

/-- Equality of measures is precisely the volume pullback identity. The
measure μ is the original Riemannian measure, characterized by its already
constructed compact-density integral, not an assumed polar formula. The
right hand side omits the basepoint and cut locus, as the polar diffeomorphism
does. The separate cut-null goal supplies their removal for ball integrals. -/
def polar_measureType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S), 2 ≤ n →
    LengthMetricComplete g → ∀ C : Connection (tangentBundle S), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ p : M,
      letI : MeasurableSpace M := borel M
      ∀ μ : Measure M,
        (∀ f : CompactlySupportedContinuousMap M ℝ, (∫ x, f x ∂μ) = P202.VolumeData.integral g f) →
        μ.Regular → (∀ K : Set M, IsCompact K → μ K < ⊤) →
        Measure.map (polarMap g F p)
          ((volume.prod (sphereMeasure g p)).withDensity
            (fun tv => ENNReal.ofReal (truncatedDensity g F p tv))) =
          μ.restrict (regularDomain g F p)

end P202Specs.Geometry.PolarVolumeDensity
