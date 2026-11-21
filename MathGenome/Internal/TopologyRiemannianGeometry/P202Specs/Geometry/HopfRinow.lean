import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.MetricGeodesicCompleteness
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CompleteExponentialMinimizers
import Mathlib.Topology.MetricSpace.Bounded

/-! Theorem 6.10, paper.tex:3453–3536. The model is Euclidean (no
boundary), and n is unrestricted. All distances, curves and maximal intervals
are the original upstream objects. A Levi-Civita connection and maximal
family can be chosen by their upstream existence theorems. -/
set_option autoImplicit false

namespace P202.HopfRinowData
open SmoothManifolds.AtlasData P202.MetricData P202.ConnectionData P202.GeodesicData
open Set
universe u

/-- Every actual maximal geodesic has domain all real times. -/
def GeodesicallyComplete {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S)) : Prop :=
  ∀ (w : Phase S) (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
    IsMaximalThrough S C w I q → I.carrier = univ

end P202.HopfRinowData

namespace P202Specs.Geometry.HopfRinow
open SmoothManifolds.AtlasData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.GeodesicData
  P202.CompletenessData P202.CompleteExponentialData P202.HopfRinowData
open Set
universe u

def geodesicallyCompleteType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  (S : SmoothManifold n .euclidean M) → Connection (tangentBundle S) → Prop

def geodesicallyCompleteValue : geodesicallyCompleteType := @GeodesicallyComplete

/-- The boundedness convention used by ClosedBoundedCompact is exactly
boundedness for any metric realizing the source distance and topology. -/
def closedBoundedCompact_iffType : Prop :=
  ∀ {n : ℕ} {M : Type u} [t : TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S) (p : M)
    (d : MetricSpace M), d.toUniformSpace.toTopologicalSpace = t →
    (∀ x y : M, @dist M d.toDist x y = lengthDistance g x y) →
    (ClosedBoundedCompact g p ↔
      ∀ K : Set M, IsClosed K → @Bornology.IsBounded M d.toBornology K → IsCompact K)

/-- The three equivalent conditions, minimizing segments under completeness,
and the full conclusion from a full exponential at just one center. The
center-based boundedness condition is identified with metric boundedness by
the preceding independent statement. -/
def hopf_rinowType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    (LengthMetricComplete g ↔ GeodesicallyComplete S C) ∧
    (LengthMetricComplete g ↔ ∀ p : M, ClosedBoundedCompact g p) ∧
    (LengthMetricComplete g → ∀ F : CurveFamily (Phase S), IsMaximalFamily S C F →
      ∀ p : M, MinimizingGeodesicsFrom g C F p) ∧
    (∀ F : CurveFamily (Phase S), IsMaximalFamily S C F →
      ∀ p : M, FullExponentialAt F p →
        LengthMetricComplete g ∧ GeodesicallyComplete S C ∧
        (∀ q : M, ClosedBoundedCompact g q) ∧
        (∀ q : M, MinimizingGeodesicsFrom g C F q))

end P202Specs.Geometry.HopfRinow
