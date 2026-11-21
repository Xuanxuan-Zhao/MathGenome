import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricTopology
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch02.ContinuityTests

/-!
The metric topology (paper.tex, Proposition d10:09:metric-topology).
We reuse the canonical metric, distance and balls of MetricConventions and
the paper's open-union formulation of a basis. All metrics are specified
explicitly; in particular the results also apply to empty types and subspaces.
-/

open Set Filter
open scoped Topology
universe u v

namespace D10Topology.Ch09
open D10Topology.Ch01

/-- Positive-radius balls form a basis for the topology of the given metric. -/
theorem metric_balls_basis {X : Type u} (d : MetricSpace X) :
    BasisFor (metricTopology d.toPseudoMetricSpace)
      {U : Set X | ∃ (x : X) (r : ℝ), 0 < r ∧ U = ball d.toPseudoMetricSpace x r} := by
  let := d
  apply (basis_iff_mathlib _ _).mpr
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro U ⟨x, r, _, rfl⟩
    rw [ball_eq_mathlib]
    exact Metric.isOpen_ball
  · intro x U hx hU
    obtain ⟨r, hr, hsub⟩ := (metricTopology_open_iff d.toPseudoMetricSpace U).mp hU x hx
    refine ⟨ball d.toPseudoMetricSpace x r, ⟨x, r, hr, rfl⟩, ?_, hsub⟩
    change dist x x < r
    simpa only [dist_self] using hr

/-- The induced metric on a subset is the original distance restricted to it. -/
theorem restricted_metric_distance {X : Type u} (d : MetricSpace X) (A : Set X) (a b : A) :
    distance (MetricSpace.induced (Subtype.val : A → X) Subtype.val_injective d).toPseudoMetricSpace a b =
      distance d.toPseudoMetricSpace a.val b.val := rfl

/-- This restriction induces exactly the subspace topology. -/
theorem restricted_metric_topology {X : Type u} (d : MetricSpace X) (A : Set X) :
    metricTopology
      (MetricSpace.induced (Subtype.val : A → X) Subtype.val_injective d).toPseudoMetricSpace =
      TopologicalSpace.induced (Subtype.val : A → X) (metricTopology d.toPseudoMetricSpace) := rfl

theorem metric_hausdorff {X : Type u} (d : MetricSpace X) :
    @T2Space X (metricTopology d.toPseudoMetricSpace) := by
  let := d
  change T2Space X
  infer_instance

theorem metric_first_countable {X : Type u} (d : MetricSpace X) :
    @FirstCountableTopology X (metricTopology d.toPseudoMetricSpace) := by
  let := d
  change FirstCountableTopology X
  infer_instance

/-- Delta may depend on both the point and epsilon. -/
theorem metric_continuousAt_iff {X : Type u} {Y : Type v}
    (d : MetricSpace X) (e : MetricSpace Y) (f : X → Y) (x : X) :
    @ContinuousAt X Y (metricTopology d.toPseudoMetricSpace)
      (metricTopology e.toPseudoMetricSpace) f x ↔
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y : X, distance d.toPseudoMetricSpace y x < δ →
        distance e.toPseudoMetricSpace (f y) (f x) < ε := by
  let := d
  let := e
  exact Metric.continuousAt_iff

/-- Continuity is precisely pointwise epsilon-delta continuity. -/
theorem metric_continuous_iff {X : Type u} {Y : Type v}
    (d : MetricSpace X) (e : MetricSpace Y) (f : X → Y) :
    @Continuous X Y (metricTopology d.toPseudoMetricSpace)
      (metricTopology e.toPseudoMetricSpace) f ↔
    ∀ x : X, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y : X, distance d.toPseudoMetricSpace y x < δ →
        distance e.toPseudoMetricSpace (f y) (f x) < ε := by
  let := d
  let := e
  rw [D10Topology.Ch02.continuous_iff_pointwise]
  exact forall_congr' (fun x => metric_continuousAt_iff d e f x)

theorem metric_closure_iff_balls {X : Type u} (d : MetricSpace X) (A : Set X) (x : X) :
    x ∈ @closure X (metricTopology d.toPseudoMetricSpace) A ↔
      ∀ r : ℝ, 0 < r → (ball d.toPseudoMetricSpace x r ∩ A).Nonempty := by
  let := d
  rw [Metric.mem_closure_iff]
  constructor
  · intro h r hr
    obtain ⟨y, hy, hdist⟩ := h r hr
    exact ⟨y, hdist, hy⟩
  · intro h r hr
    obtain ⟨y, hdist, hy⟩ := h r hr
    exact ⟨y, hy, hdist⟩

theorem metric_sequence_iff_distance_zero {X : Type u} (d : MetricSpace X)
    (s : ℕ → X) (x : X) :
    Tendsto s atTop (@nhds X (metricTopology d.toPseudoMetricSpace) x) ↔
      Tendsto (fun n => distance d.toPseudoMetricSpace (s n) x) atTop (𝓝 (0 : ℝ)) := by
  let := d
  exact tendsto_iff_dist_tendsto_zero

end D10Topology.Ch09
