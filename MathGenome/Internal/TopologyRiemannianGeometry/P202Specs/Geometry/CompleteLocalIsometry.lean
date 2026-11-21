import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CoveringMetricCompleteness

/-! The full complete-local-isometry theorem, paper.tex:4498–4542.
The topologies, smooth structures, intrinsic differentials and length distances
are the upstream ones. The forward statement permits different displayed
source and target dimensions; local diffeomorphism already forces equality.
The converse allows disconnected total spaces and includes dimension zero. -/
set_option autoImplicit false

namespace P202.CompleteLocalIsometryData
open SmoothManifolds.AtlasData SmoothManifolds.MapData
universe u

/-- An actual decomposition into disjoint open sheets with smooth maps in
both directions on their respective open domains. -/
def SmoothEvenlyCovered {n m : ℕ} {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold m .euclidean Y)
    (f : X → Y) (U : Set Y) : Prop :=
  IsOpen U ∧ ∃ A : Set (P202Specs.Topology.CoveringSheet f U),
    A.Pairwise (fun s t => Disjoint s.chart.source t.chart.source) ∧
    (⋃ s ∈ A, s.chart.source) = f ⁻¹' U ∧
    ∀ s ∈ A,
      ManifoldSmoothOn S.smoothStructure.val T.smoothStructure.val s.chart s.chart.source ∧
      ManifoldSmoothOn T.smoothStructure.val S.smoothStructure.val s.chart.symm s.chart.target

end P202.CompleteLocalIsometryData

namespace P202Specs.Geometry.CompleteLocalIsometry
open SmoothManifolds.AtlasData P202.MetricData P202.CompletenessData
  P202.CompleteLocalIsometryData
universe u

/-- Completeness of the source, with no completeness assumption on the target,
gives a surjective covering and smooth evenly covered neighborhoods. -/
def complete_local_isometryType : Prop :=
  ∀ {n m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [ConnectedSpace X] [ConnectedSpace Y]
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold m .euclidean Y)
    (g : RiemannianMetric S) (h : RiemannianMetric T) (f : X → Y),
    IsLocalIsometry g h f → LengthMetricComplete g →
      P202Specs.Topology.Covering f ∧
      ∀ y : Y, ∃ U : Set Y, y ∈ U ∧ SmoothEvenlyCovered S T f U

/-- The converse retains the full upstream pullback formula and componentwise
completeness, even when the total space is disconnected. -/
def covering_completeType : Prop :=
  P202Specs.Geometry.CoveringMetricCompleteness.covering_completeType.{u}

end P202Specs.Geometry.CompleteLocalIsometry
