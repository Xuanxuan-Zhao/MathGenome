import MathGenome.SmoothManifolds.Topics.SmoothManifolds.Ch05
import Mathlib.Analysis.Real.Sqrt

/-! Metric objects on the intrinsic derivation tangent fibers of P104.
The choices below are choices of *proved* tangent-bundle realizations, not
additional geometric hypotheses. Both allowed model kinds and rank zero remain
unrestricted. No candidate implementation is imported here. -/
set_option autoImplicit false

namespace P202.MetricData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.TangentData
  SmoothManifolds.TangentBundleData SmoothManifolds.DifferentialData
  SmoothManifolds.BundleOperationsData SmoothManifolds.BundleMetricData
universe u

noncomputable def tangentStructure {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) : TangentBundleStructure S :=
  Classical.choice (SmoothManifolds.TangentBundle.exists_bundle S)

noncomputable def tangentRealization {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) :
    TangentRealization (tangentStructure S) :=
  Classical.choice (SmoothManifolds.BundleOperations.exists_tangentRealization S
    (tangentStructure S))

noncomputable instance tangentTopology {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) :
    TopologicalSpace (Bundle.TotalSpace (Euclidean n) (TangentSpace S)) :=
  (tangentRealization S).space.topology

/-- A smooth symmetric positive-definite bilinear form on every actual tangent
fiber. Smoothness is the Gram-coefficient condition in the canonical smooth
linear tangent trivializations; these realize the original tangent atlas. -/
def RiemannianMetric {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) : Type u :=
  letI := (tangentRealization S).space.topology
  SmoothFiberMetric (tangentRealization S).space.bundle

section Metrics
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}

def pairing (g : RiemannianMetric S) (p : M) :
    LinearMap.BilinForm ℝ (TangentSpace S p) := g.form p

noncomputable def tangentNorm (g : RiemannianMetric S) (p : M)
    (v : TangentSpace S p) : ℝ := Real.sqrt (pairing g p v v)

/-- The smooth map and its intrinsic, injective tangent differentials. -/
structure SmoothImmersion (S : SmoothManifold n a M)
    (T : SmoothManifold m b N) (f : M → N) where
  smooth : IsSmoothMap S T f
  differential : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)
  isDifferential : ∀ p, IsDifferential S T f p (differential p)
  injective : ∀ p, Function.Injective (differential p)

/-- The bilinear pullback is defined for every family of tangent linear maps.
Its smoothness and positivity under a smooth immersion are theorem obligations. -/
def pullbackForm (g : RiemannianMetric T) (f : M → N)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (p : M) : LinearMap.BilinForm ℝ (TangentSpace S p) :=
  (g.form (f p)).compl₁₂ (L p) (L p)

def IsMetricPreserving (g : RiemannianMetric S) (h : RiemannianMetric T)
    (f : M → N)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)) : Prop :=
  ∀ p v w, pairing h (f p) (L p v) (L p w) = pairing g p v w

def IsIsometricImmersion (g : RiemannianMetric S) (h : RiemannianMetric T)
    (f : M → N) : Prop :=
  ∃ i : SmoothImmersion S T f, IsMetricPreserving g h f i.differential

/-- A metric-preserving local diffeomorphism, with its actual intrinsic
 differential. Local inverses are those of the original P104 smooth structures. -/
def IsLocalIsometry (g : RiemannianMetric S) (h : RiemannianMetric T)
    (f : M → N) : Prop :=
  SmoothManifolds.TensorData.IsLocalDiffeomorphism S T f ∧
  ∃ L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p),
    (∀ p, IsDifferential S T f p (L p)) ∧ IsMetricPreserving g h f L

end Metrics
end P202.MetricData

namespace P202Specs.Geometry.SmoothMetrics
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

/- These laws concern the norm constructed from the metric, not extra data. -/

def tangentNorm_nonnegType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M},
  ∀ (g : RiemannianMetric S) (p : M) (v : TangentSpace S p),
    0 ≤ tangentNorm g p v

def tangentNorm_zeroType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M},
  ∀ (g : RiemannianMetric S) (p : M), tangentNorm g p 0 = 0

def tangentNorm_sqType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M},
  ∀ (g : RiemannianMetric S) (p : M) (v : TangentSpace S p),
    tangentNorm g p v ^ 2 = pairing g p v v

def tangentNorm_eq_zero_iffType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M},
  ∀ (g : RiemannianMetric S) (p : M) (v : TangentSpace S p),
    tangentNorm g p v = 0 ↔ v = 0

def tangentNorm_negType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M},
  ∀ (g : RiemannianMetric S) (p : M) (v : TangentSpace S p),
    tangentNorm g p (-v) = tangentNorm g p v

def tangentNorm_smulType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M},
  ∀ (g : RiemannianMetric S) (p : M) (c : ℝ) (v : TangentSpace S p),
    tangentNorm g p (c • v) = |c| * tangentNorm g p v


def metricPreserving_normType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N},
  ∀ (g : RiemannianMetric S) (h : RiemannianMetric T) (f : M → N)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)),
    IsMetricPreserving g h f L → ∀ (p : M) (v : TangentSpace S p),
      tangentNorm h (f p) (L p v) = tangentNorm g p v

def localIsometry_isIsometricImmersionType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N},
  ∀ (g : RiemannianMetric S) (h : RiemannianMetric T) (f : M → N),
    IsLocalIsometry g h f → IsIsometricImmersion g h f

end P202Specs.Geometry.SmoothMetrics
