import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.HopfRinow
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Cut time, cut point and cut locus: paper.tex:4185–4200. The sphere uses
actual tangent vectors with the original metric norm. The supremum is taken in
ℝ≥0∞, so an unbounded minimizing ray has cut time ∞. The underlying manifold
model is Euclidean (without boundary). -/
open scoped ENNReal

set_option autoImplicit false

namespace P202.CutTimeData
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData P202.MetricData P202.GeodesicData
  P202.ExponentialData P202.CompleteExponentialData
open Set
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- The unit sphere of the actual metric tangent fiber. -/
def UnitDirection (g : RiemannianMetric S) (p : M) :=
  {v : TangentSpace S p // tangentNorm g p v = 1}

/-- Nonnegative times at which the radial segment realizes distance. -/
def minimizingTimes (g : RiemannianMetric S) (F : CurveFamily (Phase S))
    (p : M) (v : UnitDirection g p) : Set ℝ :=
  {t | 0 ≤ t ∧ lengthDistance g p (fiberExponential F p (t • v.val)) = t}

noncomputable def cutTime (g : RiemannianMetric S) (F : CurveFamily (Phase S))
    (p : M) (v : UnitDirection g p) : ℝ≥0∞ :=
  sSup (ENNReal.ofReal '' minimizingTimes g F p v)

/-- A cut point is defined only for a finite cut direction. -/
noncomputable def cutPoint (g : RiemannianMetric S) (F : CurveFamily (Phase S))
    (p : M) (v : UnitDirection g p) (_h : cutTime g F p v ≠ ⊤) : M :=
  fiberExponential F p ((cutTime g F p v).toReal • v.val)

/-- Union of the endpoints of all finite cut directions. -/
def cutLocus (g : RiemannianMetric S) (F : CurveFamily (Phase S)) (p : M) : Set M :=
  {q | ∃ (v : UnitDirection g p) (h : cutTime g F p v ≠ ⊤),
    cutPoint g F p v h = q}

/-- Strictly positive radii strictly below their (possibly infinite) cut time. -/
def polarDomain (g : RiemannianMetric S) (F : CurveFamily (Phase S))
    (p : M) : Set (ℝ × UnitDirection g p) :=
  {tv | 0 < tv.1 ∧ ENNReal.ofReal tv.1 < cutTime g F p tv.2}

end P202.CutTimeData

namespace P202Specs.Geometry.CutTime
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData P202.MetricData P202.ConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.ExponentialData
  P202.CompletenessData P202.CompleteExponentialData P202.CutTimeData
open Set
universe u

def unitDirectionType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → RiemannianMetric S → M → Type u
def unitDirectionValue : unitDirectionType := @UnitDirection

def minimizingTimesType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → (g : RiemannianMetric S) →
  CurveFamily (Phase S) → (p : M) → UnitDirection g p → Set ℝ
def minimizingTimesValue : minimizingTimesType := @minimizingTimes

def cutTimeType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → (g : RiemannianMetric S) →
  CurveFamily (Phase S) → (p : M) → UnitDirection g p → ℝ≥0∞
noncomputable def cutTimeValue : cutTimeType := @cutTime

def cutPointType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → (g : RiemannianMetric S) →
  (F : CurveFamily (Phase S)) → (p : M) → (v : UnitDirection g p) →
  cutTime g F p v ≠ ⊤ → M
noncomputable def cutPointValue : cutPointType := @cutPoint

def cutLocusType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → RiemannianMetric S →
  CurveFamily (Phase S) → M → Set M
def cutLocusValue : cutLocusType := @cutLocus

def polarDomainType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → (g : RiemannianMetric S) →
  CurveFamily (Phase S) → (p : M) → Set (ℝ × UnitDirection g p)
def polarDomainValue : polarDomainType := @polarDomain

/-- The required auxiliary choices exist on every complete manifold. In
particular the use of an arbitrary correct maximal family below adds no
existence hypothesis on the original manifold. -/
def complete_exponential_existsType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S),
    LengthMetricComplete g → ∃ (C : Connection (tangentBundle S))
      (F : CurveFamily (Phase S)), IsLeviCivita g C ∧ IsMaximalFamily S C F ∧
      ∀ p : M, FullExponentialAt F p

/-- The equality set is exactly the closed initial interval, with the finite
endpoint included; for infinite cut time all nonnegative times minimize.
The positive-dimensional source hypothesis is explicit. -/
def cut_time_intervalType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S), 0 < n →
    LengthMetricComplete g → ∀ (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ (p : M) (v : UnitDirection g p),
      FullExponentialAt F p ∧ 0 < cutTime g F p v ∧
      IsClosed (minimizingTimes g F p v) ∧
      (∀ t : ℝ, t ∈ minimizingTimes g F p v ↔
        0 ≤ t ∧ ENNReal.ofReal t ≤ cutTime g F p v) ∧
      (∀ h : cutTime g F p v ≠ ⊤,
        minimizingTimes g F p v = Icc 0 (cutTime g F p v).toReal ∧
        0 < (cutTime g F p v).toReal ∧
        lengthDistance g p (cutPoint g F p v h) = (cutTime g F p v).toReal) ∧
      (cutTime g F p v = ⊤ → minimizingTimes g F p v = Ici 0)

end P202Specs.Geometry.CutTime
