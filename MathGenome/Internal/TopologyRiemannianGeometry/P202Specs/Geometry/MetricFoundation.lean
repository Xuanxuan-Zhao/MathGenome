import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.LengthLaws

/-! Independent specification of the metric foundation. The canonical metric
and curve objects come from the three prerequisite Specs. In particular this
module introduces no second tangent model and no assumed proof certificates.
The theorem types below unfold to the full upstream propositions. -/
set_option autoImplicit false

namespace P202Specs.Geometry.MetricFoundation
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData P202.MetricData
universe u

def metricType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → SmoothManifold n a M → Type u

def metricValue : metricType := @P202.MetricData.RiemannianMetric

def pairingType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} →
  RiemannianMetric S → (p : M) → LinearMap.BilinForm ℝ (TangentSpace S p)

def pairingValue : pairingType := @P202.MetricData.pairing

def normType := {n : ℕ} → {a : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n a M} →
  RiemannianMetric S → (p : M) → TangentSpace S p → ℝ

noncomputable def normValue : normType := @P202.MetricData.tangentNorm

def immersionType := {n m : ℕ} → {a b : ModelKind} → {M N : Type u} →
  [TopologicalSpace M] → [TopologicalSpace N] →
  SmoothManifold n a M → SmoothManifold m b N → (M → N) → Type u

def immersionValue : immersionType := @P202.MetricData.SmoothImmersion

def pullbackFormType := {n m : ℕ} → {a b : ModelKind} → {M N : Type u} →
  [TopologicalSpace M] → [TopologicalSpace N] →
  {S : SmoothManifold n a M} → {T : SmoothManifold m b N} →
  RiemannianMetric T → (f : M → N) →
  ((p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)) →
  (p : M) → LinearMap.BilinForm ℝ (TangentSpace S p)

def pullbackFormValue : pullbackFormType := @P202.MetricData.pullbackForm

def metricPreservingType := {n m : ℕ} → {a b : ModelKind} → {M N : Type u} →
  [TopologicalSpace M] → [TopologicalSpace N] →
  {S : SmoothManifold n a M} → {T : SmoothManifold m b N} →
  RiemannianMetric S → RiemannianMetric T → (f : M → N) →
  ((p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)) → Prop

def metricPreservingValue : metricPreservingType := @P202.MetricData.IsMetricPreserving

def isometricImmersionType := {n m : ℕ} → {a b : ModelKind} → {M N : Type u} →
  [TopologicalSpace M] → [TopologicalSpace N] →
  {S : SmoothManifold n a M} → {T : SmoothManifold m b N} →
  RiemannianMetric S → RiemannianMetric T → (M → N) → Prop

def isometricImmersionValue : isometricImmersionType := @P202.MetricData.IsIsometricImmersion

def localIsometryType := {n m : ℕ} → {a b : ModelKind} → {M N : Type u} →
  [TopologicalSpace M] → [TopologicalSpace N] →
  {S : SmoothManifold n a M} → {T : SmoothManifold m b N} →
  RiemannianMetric S → RiemannianMetric T → (M → N) → Prop

def localIsometryValue : localIsometryType := @P202.MetricData.IsLocalIsometry

def exists_metricType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M), Nonempty (RiemannianMetric S)

def pullback_metricType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N) (i : SmoothImmersion S T f) (h : RiemannianMetric T),
    ∃ g : RiemannianMetric S, ∀ p v w,
      pairing g p v w = pairing h (f p) (i.differential p v) (i.differential p w)

/-- The concrete immersion data is equivalent to the original P104 immersion
predicate together with smoothness; injectivity of the map itself is absent. -/
def smoothImmersion_iffType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N),
    Nonempty (SmoothImmersion S T f) ↔
      SmoothManifolds.MapData.IsSmoothMap S T f ∧
        SmoothManifolds.MapClassData.IsImmersion S T f

/-- Pullback stated using the original map-class predicate and the actual
canonical differential of a smooth map. -/
def pullback_metric_originalType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N)
    (hf : SmoothManifolds.MapData.IsSmoothMap S T f),
    SmoothManifolds.MapClassData.IsImmersion S T f →
    ∀ h : RiemannianMetric T, ∃ g : RiemannianMetric S, ∀ p v w,
      pairing g p v w = pairing h (f p)
        (SmoothManifolds.differential S T f hf p v)
        (SmoothManifolds.differential S T f hf p w)



abbrev coordinateC1OnType := P202Specs.Geometry.PiecewiseCurves.coordinateC1OnType.{u}
def coordinateC1OnValue : coordinateC1OnType := @P202.CurveData.CoordinateC1On

abbrev piecewiseC1CurveType := P202Specs.Geometry.PiecewiseCurves.piecewiseC1CurveType.{u}
def piecewiseC1CurveValue : piecewiseC1CurveType := @P202.CurveData.PiecewiseC1Curve

abbrev compactPiecewiseC1CurveType := P202Specs.Geometry.PiecewiseCurves.compactPiecewiseC1CurveType.{u}
def compactPiecewiseC1CurveValue : compactPiecewiseC1CurveType := @P202.CurveData.CompactPiecewiseC1Curve

abbrev breakpointsType := P202Specs.Geometry.PiecewiseCurves.breakpointsType.{u}
noncomputable def breakpointsValue : breakpointsType := @P202.CurveData.breakpoints

abbrev compactCurveType := P202Specs.Geometry.PiecewiseCurves.compactCurveType.{u}
def compactCurveValue : compactCurveType := @P202.CurveData.compactCurve

abbrev hasVelocityAtType := P202Specs.Geometry.PiecewiseCurves.hasVelocityAtType.{u}
def hasVelocityAtValue : hasVelocityAtType := @P202.CurveData.HasVelocityAt

abbrev velocityType := P202Specs.Geometry.PiecewiseCurves.velocityType.{u}
noncomputable def velocityValue : velocityType := @P202.CurveData.velocity

abbrev speedType := P202Specs.Geometry.PiecewiseCurves.speedType.{u}
noncomputable def speedValue : speedType := @P202.CurveData.speed

abbrev lengthType := P202Specs.Geometry.PiecewiseCurves.lengthType.{u}
noncomputable def lengthValue : lengthType := @P202.CurveData.length

abbrev energyType := P202Specs.Geometry.PiecewiseCurves.energyType.{u}
noncomputable def energyValue : energyType := @P202.CurveData.energy

abbrev piecewiseRegularIncreasingType := P202Specs.Geometry.PiecewiseCurves.piecewiseRegularIncreasingType
def piecewiseRegularIncreasingValue : piecewiseRegularIncreasingType := @P202.CurveData.PiecewiseRegularIncreasing

abbrev regularRealC1OnType := P202Specs.Geometry.PiecewiseCurves.regularRealC1OnType
def regularRealC1OnValue : regularRealC1OnType := @P202.CurveData.RegularRealC1On

abbrev parameterToFunType := P202Specs.Geometry.PiecewiseCurves.parameterToFunType
noncomputable def parameterToFunValue : parameterToFunType := @P202.CurveData.PiecewiseRegularIncreasing.toFun

def tangentNorm_nonnegType : Prop :=
  P202Specs.Geometry.SmoothMetrics.tangentNorm_nonnegType.{u}

def tangentNorm_zeroType : Prop :=
  P202Specs.Geometry.SmoothMetrics.tangentNorm_zeroType.{u}

def tangentNorm_sqType : Prop :=
  P202Specs.Geometry.SmoothMetrics.tangentNorm_sqType.{u}

def tangentNorm_eq_zero_iffType : Prop :=
  P202Specs.Geometry.SmoothMetrics.tangentNorm_eq_zero_iffType.{u}

def tangentNorm_negType : Prop :=
  P202Specs.Geometry.SmoothMetrics.tangentNorm_negType.{u}

def tangentNorm_smulType : Prop :=
  P202Specs.Geometry.SmoothMetrics.tangentNorm_smulType.{u}

def metricPreserving_normType : Prop :=
  P202Specs.Geometry.SmoothMetrics.metricPreserving_normType.{u}

def localIsometry_isIsometricImmersionType : Prop :=
  P202Specs.Geometry.SmoothMetrics.localIsometry_isIsometricImmersionType.{u}

def hasVelocityAt_coordinatesType : Prop :=
  P202Specs.Geometry.PiecewiseCurves.hasVelocityAt_coordinatesType.{u}

def hasVelocityAt_uniqueType : Prop :=
  P202Specs.Geometry.PiecewiseCurves.hasVelocityAt_uniqueType.{u}

def hasVelocityAt_off_breakpointsType : Prop :=
  P202Specs.Geometry.PiecewiseCurves.hasVelocityAt_off_breakpointsType.{u}

def velocity_eq_coordinateExtensionType : Prop :=
  P202Specs.Geometry.PiecewiseCurves.velocity_eq_coordinateExtensionType.{u}

def coordinateExtension_independentType : Prop :=
  P202Specs.Geometry.PiecewiseCurves.coordinateExtension_independentType.{u}

def speed_integrableType : Prop :=
  P202Specs.Geometry.PiecewiseCurves.speed_integrableType.{u}

def squared_speed_integrableType : Prop :=
  P202Specs.Geometry.PiecewiseCurves.squared_speed_integrableType.{u}

def length_eq_of_eqOnType : Prop :=
  P202Specs.Geometry.PiecewiseCurves.length_eq_of_eqOnType.{u}

def energy_eq_of_eqOnType : Prop :=
  P202Specs.Geometry.PiecewiseCurves.energy_eq_of_eqOnType.{u}

def integral_norm_eq_of_velocity_eqOn_off_finiteType : Prop :=
  P202Specs.Geometry.PiecewiseCurves.integral_norm_eq_of_velocity_eqOn_off_finiteType.{u}

def integral_sq_norm_eq_of_velocity_eqOn_off_finiteType : Prop :=
  P202Specs.Geometry.PiecewiseCurves.integral_sq_norm_eq_of_velocity_eqOn_off_finiteType.{u}

def length_degenerateType : Prop :=
  P202Specs.Geometry.PiecewiseCurves.length_degenerateType.{u}

def energy_degenerateType : Prop :=
  P202Specs.Geometry.PiecewiseCurves.energy_degenerateType.{u}

def stationary_existsType : Prop :=
  P202Specs.Geometry.PiecewiseCurves.stationary_existsType.{u}

def compact_representationType : Prop :=
  P202Specs.Geometry.PiecewiseCurves.compact_representationType.{u}

def restriction_existsType : Prop :=
  P202Specs.Geometry.PiecewiseCurves.restriction_existsType.{u}

def postcomposition_existsType : Prop :=
  P202Specs.Geometry.PiecewiseCurves.postcomposition_existsType.{u}

def concatenation_existsType : Prop :=
  P202Specs.Geometry.PiecewiseCurves.concatenation_existsType.{u}

def reversal_existsType : Prop :=
  P202Specs.Geometry.PiecewiseCurves.reversal_existsType.{u}

def reparametrization_existsType : Prop :=
  P202Specs.Geometry.PiecewiseCurves.reparametrization_existsType.{u}

def isometricImmersion_lengthType : Prop :=
  P202Specs.Geometry.LengthLaws.isometricImmersion_lengthType.{u}

def localIsometry_lengthType : Prop :=
  P202Specs.Geometry.LengthLaws.localIsometry_lengthType.{u}

def localIsometry_length_existsType : Prop :=
  P202Specs.Geometry.LengthLaws.localIsometry_length_existsType.{u}

def subdivision_lengthType : Prop :=
  P202Specs.Geometry.LengthLaws.subdivision_lengthType.{u}

def subdivision_length_existsType : Prop :=
  P202Specs.Geometry.LengthLaws.subdivision_length_existsType.{u}

def finiteConcatenation_lengthType : Prop :=
  P202Specs.Geometry.LengthLaws.finiteConcatenation_lengthType.{u}

def concatenation_lengthType : Prop :=
  P202Specs.Geometry.LengthLaws.concatenation_lengthType.{u}

def reversal_lengthType : Prop :=
  P202Specs.Geometry.LengthLaws.reversal_lengthType.{u}

def reversal_length_existsType : Prop :=
  P202Specs.Geometry.LengthLaws.reversal_length_existsType.{u}

def reparametrization_lengthType : Prop :=
  P202Specs.Geometry.LengthLaws.reparametrization_lengthType.{u}

def reparametrization_length_existsType : Prop :=
  P202Specs.Geometry.LengthLaws.reparametrization_length_existsType.{u}

/-- The velocity is intrinsic and the integral is the real interval integral. -/
def length_formulaType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    {a b : ℝ} (c : P202.CurveData.PiecewiseC1Curve S a b),
    P202.CurveData.length g c =
      ∫ t in a..b, tangentNorm g (c t) (P202.CurveData.velocity S c t)

def energy_formulaType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    {a b : ℝ} (c : P202.CurveData.PiecewiseC1Curve S a b),
    P202.CurveData.energy g c =
      (1 / 2 : ℝ) * ∫ t in a..b,
        (tangentNorm g (c t) (P202.CurveData.velocity S c t)) ^ 2

end P202Specs.Geometry.MetricFoundation
