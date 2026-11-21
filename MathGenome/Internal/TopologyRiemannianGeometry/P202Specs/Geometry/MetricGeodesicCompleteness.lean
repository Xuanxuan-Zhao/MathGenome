import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.LengthDistance
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GeodesicIVP
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.ClusterPt

/-! The metric-completeness implication in Theorem 6.10 (Hopf--Rinow),
paper.tex:3453–3483. The distance is the original length infimum, on the
original manifold, and the phase space is the original intrinsic tangent bundle.
All dimensions, including zero, and all initial velocities are included. -/
set_option autoImplicit false

namespace P202.CompletenessData
open SmoothManifolds.AtlasData P202.MetricData P202.DistanceData
open Set
universe u

/-- Completeness of the length metric, with its original manifold topology.
The existential metric structure supplies only the distance and uniformity;
no tangent-bundle completeness or compactness is assumed. -/
def LengthMetricComplete {n : ℕ} {M : Type u} [t : TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S) : Prop :=
  ∃ d : MetricSpace M,
    d.toUniformSpace.toTopologicalSpace = t ∧
    (∀ p q : M, @dist M d.toDist p q = sInf (pathLengths g p q)) ∧
    @CompleteSpace M d.toUniformSpace

end P202.CompletenessData

namespace P202Specs.Geometry.MetricGeodesicCompleteness
open SmoothManifolds.AtlasData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData
  P202.GeodesicData P202.CompletenessData
open Set Filter
open scoped Topology
universe u

def lengthMetricCompleteType := {n : ℕ} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n .euclidean M} →
  RiemannianMetric S → Prop

def lengthMetricCompleteValue : lengthMetricCompleteType := @LengthMetricComplete

/-- The full assigned implication. Maximality concerns both position and
actual velocity on the open interval, not just a representative in coordinates. -/
def metric_complete_geodesically_completeType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    LengthMetricComplete g →
    ∀ (w : Phase S) (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
      IsMaximalThrough S C w I q → I.carrier = univ

/-- The actual position/velocity state has a limit in the intrinsic tangent
bundle at every real time after continuation. -/
def metric_complete_phase_limitType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    LengthMetricComplete g →
    ∀ (w : Phase S) (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
      IsMaximalThrough S C w I q →
      ∀ b : ℝ, Tendsto q (𝓝[I.carrier] b) (𝓝 (q b))

/-- A finite time carrying a cluster state in the actual tangent bundle lies
inside the maximal domain. This continuation lemma needs no metric. -/
def time_mem_of_phase_clusterType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S))
    (w : Phase S) (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
    IsMaximalThrough S C w I q →
    ∀ (b : ℝ) (z : Phase S), MapClusterPt z (𝓝[I.carrier] b) q → b ∈ I.carrier

/-- A maximal geodesic with a phase cluster state at every finite boundary
time has no boundary times, hence has domain all of the real line. -/
def global_of_phase_clustersType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S))
    (w : Phase S) (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
    IsMaximalThrough S C w I q →
    (∀ b ∈ closure I.carrier, ∃ z : Phase S,
      MapClusterPt z (𝓝[I.carrier] b) q) → I.carrier = univ

/-- The zero-velocity case does not require metric completeness. -/
def zero_velocity_globalType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S))
    (p : M) (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
    IsMaximalThrough S C ⟨p, 0⟩ I q →
      I.carrier = univ ∧ EqOn q (constantCurve S p) I.carrier

end P202Specs.Geometry.MetricGeodesicCompleteness
