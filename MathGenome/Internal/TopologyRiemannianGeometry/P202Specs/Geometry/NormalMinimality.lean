import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GaussLemma
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.LengthDistance

/-! Centered normal-ball part of Theorem 6.9, paper.tex:3372–3374,
3396–3411. The distance and competitors are the original global ones.
The radius parameter below includes pauses, zero velocities, repeated visits
to the center, and degenerate parameter intervals. No assertion is made about
total representatives outside their compact parameter intervals. -/
set_option autoImplicit false

namespace P202.NormalMinimalityData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.CurveData P202.GeodesicData P202.ExponentialData
open Set
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- An actual continuous, nondecreasing radius parameter, rather than a
regular change of parameter. Division by zero is harmless for v = 0: the
represented curve is then the constant exponential of the zero vector. -/
def RadialParametrization (g : RiemannianMetric S) (F : CurveFamily (Phase S))
    (p : M) (v : TangentSpace S p) (a b : ℝ) (γ : ℝ → M) : Prop :=
  ∃ ρ : ℝ → ℝ, ContinuousOn ρ (Icc a b) ∧ MonotoneOn ρ (Icc a b) ∧
    ρ a = 0 ∧ ρ b = tangentNorm g p v ∧
    ∀ t ∈ Icc a b, γ t =
      fiberExponential F p ((ρ t / tangentNorm g p v) • v)

end P202.NormalMinimalityData

namespace P202Specs.Geometry.NormalMinimality
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.ConnectionData P202.CurveData P202.GeodesicData
  P202.LeviCivitaData P202.ExponentialData P202.DistanceData
  P202.NormalMinimalityData
open Set
universe u

def RadialParametrizationType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → RiemannianMetric S →
  CurveFamily (Phase S) → (p : M) → TangentSpace S p → ℝ → ℝ → (ℝ → M) → Prop
def RadialParametrizationValue : RadialParametrizationType := @RadialParametrization

/-- The larger open ball contains the entire closed radius-r₀ ball since
r₀ < R. Smoothness, the actual exponential domain and both inverse laws are
part of the upstream definition of IsNormalChart. -/
def normal_radius_existsType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ p : M, ∃ (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
      (r₀ R : ℝ) (d : ModelChart n .euclidean M),
      IsOrthonormalCoordinates g p E ∧ 0 < r₀ ∧ r₀ < R ∧ IsNormalChart g F p E R d

/-- A genuine curve in the canonical piecewise C¹ class, with actual geodesic
lift and its length. The constant radial segment is included. -/
def radial_segment_existsType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
      (R : ℝ) (d : ModelChart n .euclidean M), IsNormalChart g F p E R d →
    ∀ v : TangentSpace S p, tangentNorm g p v < R →
      ∃ γ : PiecewiseC1Curve S 0 1,
        γ 0 = p ∧ γ 1 = fiberExponential F p v ∧
        EqOn γ (fun t => fiberExponential F p (t • v)) (Icc 0 1) ∧
        EqOn γ (fun t => (F.curve ⟨p, v⟩ t).1) (Icc 0 1) ∧
        IsGeodesicOn S C (Icc 0 1) (F.curve ⟨p, v⟩) ∧
        length g γ = tangentNorm g p v

/-- The global comparison and escape estimate needed for assembly.
This is an obligation, not an assumption in normal_minimalityType. -/
def global_comparisonType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
      (r₀ R : ℝ) (d : ModelChart n .euclidean M),
      0 < r₀ → r₀ < R → IsNormalChart g F p E R d →
    ∀ v : TangentSpace S p, tangentNorm g p v < r₀ →
    ∀ {a b : ℝ} (γ : PiecewiseC1Curve S a b),
      γ a = p → γ b = fiberExponential F p v →
      tangentNorm g p v ≤ length g γ ∧
        (length g γ < r₀ → ∀ t ∈ Icc a b, γ t ∈ d.source)

/-- Equality for curves within any normal chart. No regularity or
nonvanishing-speed condition is added to the original curve class. -/
def chart_rigidityType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
      (R : ℝ) (d : ModelChart n .euclidean M), IsNormalChart g F p E R d →
    ∀ v : TangentSpace S p, tangentNorm g p v < R →
    ∀ {a b : ℝ} (γ : PiecewiseC1Curve S a b),
      γ a = p → γ b = fiberExponential F p v →
      (∀ t ∈ Icc a b, γ t ∈ d.source) → length g γ = tangentNorm g p v →
      RadialParametrization g F p v a b γ

/-- Full centered normal-ball conclusion. Every competitor lives in M; its
image is unrestricted. For equality, image equality is explicit in addition
to the radius parametrization. The case q = p explicitly gives a point image.
The distance is on the actual connected component, with membership proved. -/
def normal_minimalityType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ p : M, ∃ (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
      (r₀ R : ℝ) (d : ModelChart n .euclidean M),
      IsOrthonormalCoordinates g p E ∧ 0 < r₀ ∧ r₀ < R ∧ IsNormalChart g F p E R d ∧
    ∀ v : TangentSpace S p, tangentNorm g p v < r₀ →
      (∃ γ : PiecewiseC1Curve S 0 1,
        γ 0 = p ∧ γ 1 = fiberExponential F p v ∧
        EqOn γ (fun t => fiberExponential F p (t • v)) (Icc 0 1) ∧
        IsGeodesicOn S C (Icc 0 1) (F.curve ⟨p, v⟩) ∧
        length g γ = tangentNorm g p v) ∧
      (∃ hq : fiberExponential F p v ∈ connectedComponent p,
        componentDistance g p ⟨p, mem_connectedComponent⟩
          ⟨fiberExponential F p v, hq⟩ = tangentNorm g p v) ∧
      ∀ {a b : ℝ} (γ : PiecewiseC1Curve S a b),
        γ a = p → γ b = fiberExponential F p v →
        tangentNorm g p v ≤ length g γ ∧
        (length g γ = tangentNorm g p v →
          RadialParametrization g F p v a b γ ∧
          γ '' Icc a b = (fun t : ℝ => fiberExponential F p (t • v)) '' Icc 0 1 ∧
          (fiberExponential F p v = p → ∀ t ∈ Icc a b, γ t = p))

/-- Assembly interface only. The two antecedents remain proof obligations;
the unconditional original conclusion is normal_minimalityType. -/
def normal_minimality_of_comparison_and_rigidityType : Prop :=
  global_comparisonType.{u} → chart_rigidityType.{u} → normal_minimalityType.{u}

end P202Specs.Geometry.NormalMinimality
