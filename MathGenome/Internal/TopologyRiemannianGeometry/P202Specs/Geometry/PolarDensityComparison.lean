import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PolarVolumeDensity
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ConstantCurvaturePolar
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.RicciScalarBianchi

/-! The directionwise comparison stages of Bishop--Gromov,
paper.tex 4441–4472. The density and its extension by zero are exactly the
canonical objects from PolarVolumeDensity. The comparison interval is open
at the first positive zero of s_k and has no finite endpoint when k ≤ 0. -/
set_option autoImplicit false
noncomputable section
open scoped Topology ENNReal

namespace P202.PolarComparisonData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData P202.MetricData P202.ConnectionData
  P202.GeodesicData P202.CurvatureData P202.JacobiMatrixData P202.RicciData
  P202.CutTimeData P202.PolarVolumeData P202.ConstantCurvaturePolarData
universe u

/-- Exactly 0 < t < ρ_k, where ρ_k = ∞ when k ≤ 0. -/
def comparisonInterval (k : ℝ) : Set ℝ :=
  {t | 0 < t ∧ (0 < k → t < Real.pi / Real.sqrt k)}

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- The quadratic form Ric ≥ (n−1) k g on every original tangent fiber. -/
def RicciLowerBound (g : RiemannianMetric S) (R : CurvatureTensor S) (k : ℝ) : Prop :=
  ∀ p (w : TangentSpace S p),
    (n - 1 : ℕ) * k * pairing g p w w ≤ ricci R p w w

def preCutInterval (g : RiemannianMetric S) (F : CurveFamily (Phase S))
    (p : M) (v : UnitDirection g p) (k : ℝ) : Set ℝ :=
  {t | t ∈ comparisonInterval k ∧ ENNReal.ofReal t < cutTime g F p v}

def densityRatio (g : RiemannianMetric S) (F : CurveFamily (Phase S))
    (p : M) (v : UnitDirection g p) (k t : ℝ) : ℝ :=
  radialDensity g F p (t, v) / s k t ^ (n - 1)

def truncatedRatio (g : RiemannianMetric S) (F : CurveFamily (Phase S))
    (p : M) (v : UnitDirection g p) (k t : ℝ) : ℝ :=
  truncatedDensity g F p (t, v) / s k t ^ (n - 1)

/-- Normalized trace of the actual normal Riccati operator. -/
def meanTrace {C : Connection (tangentBundle S)} {R : CurvatureTensor S}
    {I : D13Unified.OpenTimeInterval} {q : ℝ → Phase S}
    (D : JacobiSystem S C R I q (n - 1)) (t : ℝ) : ℝ :=
  LinearMap.trace ℝ (Euclidean (n - 1)) (riccati D t).toLinearMap / (n - 1 : ℕ)
end P202.PolarComparisonData

namespace P202Specs.Geometry.PolarDensityComparison
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData P202.MetricData P202.ConnectionData
  P202.CurveConnectionData P202.LeviCivitaData P202.GeodesicData P202.CurvatureData
  P202.ExponentialData P202.JacobiMatrixData P202.RicciData P202.CompletenessData
  P202.CutTimeData P202.PolarVolumeData P202.ConstantCurvaturePolarData
  P202.PolarComparisonData
open Set Filter
universe u

/-- The trace argument is local along an arbitrary unit geodesic. Neither
sectional bounds nor a prepackaged scalar Riccati inequality are inputs.
The last two conclusions give θ′ + θ² + k ≤ 0 with its actual derivative. -/
def trace_riccatiType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S), 2 ≤ n →
    ∀ C : Connection (tangentBundle S), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ k : ℝ, RicciLowerBound g R k →
    ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
      IsGeodesicOn S C I.carrier q → 0 ∈ I.carrier →
      (∀ t ∈ I.carrier, pairing g (q t).1 (q t).2 (q t).2 = 1) →
    ∀ D : JacobiSystem S C R I q (n - 1), IsOrthonormalNormalFrame g D →
    ∀ t ∈ I.carrier, Function.Bijective (D.A t) →
      let U := riccati D t
      let m : ℝ := (n - 1 : ℕ)
      let h := -(LinearMap.trace ℝ (Euclidean (n - 1)) (U * U).toLinearMap +
        ricci R (q t).1 (q t).2 (q t).2) / m
      LinearMap.trace ℝ (Euclidean (n - 1)) (D.curvature t).toLinearMap =
        ricci R (q t).1 (q t).2 (q t).2 ∧
      (∀ x y, (∑ i, U x i * y i) = ∑ i, x i * U y i) ∧
      (LinearMap.trace ℝ (Euclidean (n - 1)) U.toLinearMap) ^ 2 ≤
        m * LinearMap.trace ℝ (Euclidean (n - 1)) (U * U).toLinearMap ∧
      HasDerivAt (meanTrace D) h t ∧ h + meanTrace D t ^ 2 + k ≤ 0

/-- Nonincreasing density ratio strictly before the actual cut time. -/
def preCut_comparisonType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S), 2 ≤ n →
    LengthMetricComplete g → ∀ C : Connection (tangentBundle S), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ k : ℝ, RicciLowerBound g R k →
    ∀ F : CurveFamily (Phase S), IsMaximalFamily S C F →
    ∀ (p : M) (v : UnitDirection g p),
      AntitoneOn (densityRatio g F p v k) (preCutInterval g F p v k)

/-- The genuine directionwise initial normalization. -/
def initial_limitType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S), 2 ≤ n →
    LengthMetricComplete g → ∀ C : Connection (tangentBundle S), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ k : ℝ, RicciLowerBound g R k →
    ∀ F : CurveFamily (Phase S), IsMaximalFamily S C F →
    ∀ (p : M) (v : UnitDirection g p),
      Tendsto (densityRatio g F p v k) (𝓝[>] (0 : ℝ)) (𝓝 1) ∧
      Tendsto (truncatedRatio g F p v k) (𝓝[>] (0 : ℝ)) (𝓝 1)

/-- Includes finite cut endpoints, downward jumps, and infinite cut time. -/
def truncated_comparisonType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S), 2 ≤ n →
    LengthMetricComplete g → ∀ C : Connection (tangentBundle S), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ k : ℝ, RicciLowerBound g R k →
    ∀ F : CurveFamily (Phase S), IsMaximalFamily S C F →
    ∀ (p : M) (v : UnitDirection g p),
      AntitoneOn (truncatedRatio g F p v k) (comparisonInterval k) ∧
      ∀ t ∈ comparisonInterval k, 0 ≤ truncatedRatio g F p v k t ∧
        truncatedRatio g F p v k t ≤ 1

end P202Specs.Geometry.PolarDensityComparison
