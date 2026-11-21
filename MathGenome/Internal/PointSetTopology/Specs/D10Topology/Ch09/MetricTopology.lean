import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import Mathlib.Topology.MetricSpace.Basic

/-!
Independent statements for paper.tex, Proposition d10:09:metric-topology.
The topology is always the one induced by the specified metric. Restriction
is the pullback metric on the subtype, so neither a point nor a nonemptiness
hypothesis is required. The paper's balls use distance from center to point.
-/

open Set Filter
open scoped Topology
universe u v

namespace Specs.D10Topology.Ch09.MetricTopology
open Specs.D10Topology.Ch09.MetricConventions
open Specs.D10Topology.Ch01.BasesAndNeighborhoods

def metric_balls_basis : Prop :=
  ∀ {X : Type u} (d : MetricSpace X),
    BasisFor (metricTopology d.toPseudoMetricSpace)
      {U : Set X | ∃ (x : X) (r : ℝ), 0 < r ∧ U = ball d.toPseudoMetricSpace x r}

/-- The pullback really is restriction of the specified distance. -/
def restricted_metric_distance : Prop :=
  ∀ {X : Type u} (d : MetricSpace X) (A : Set X) (a b : A),
    distance (MetricSpace.induced (Subtype.val : A → X) Subtype.val_injective d).toPseudoMetricSpace a b =
      distance d.toPseudoMetricSpace a.val b.val

def restricted_metric_topology : Prop :=
  ∀ {X : Type u} (d : MetricSpace X) (A : Set X),
    metricTopology
      (MetricSpace.induced (Subtype.val : A → X) Subtype.val_injective d).toPseudoMetricSpace =
      TopologicalSpace.induced (Subtype.val : A → X) (metricTopology d.toPseudoMetricSpace)

def metric_hausdorff : Prop :=
  ∀ {X : Type u} (d : MetricSpace X), @T2Space X (metricTopology d.toPseudoMetricSpace)

def metric_first_countable : Prop :=
  ∀ {X : Type u} (d : MetricSpace X),
    @FirstCountableTopology X (metricTopology d.toPseudoMetricSpace)

def metric_continuousAt_iff : Prop :=
  ∀ {X : Type u} {Y : Type v} (d : MetricSpace X) (e : MetricSpace Y)
    (f : X → Y) (x : X),
    @ContinuousAt X Y (metricTopology d.toPseudoMetricSpace)
      (metricTopology e.toPseudoMetricSpace) f x ↔
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y : X, distance d.toPseudoMetricSpace y x < δ →
        distance e.toPseudoMetricSpace (f y) (f x) < ε

def metric_continuous_iff : Prop :=
  ∀ {X : Type u} {Y : Type v} (d : MetricSpace X) (e : MetricSpace Y) (f : X → Y),
    @Continuous X Y (metricTopology d.toPseudoMetricSpace)
      (metricTopology e.toPseudoMetricSpace) f ↔
    ∀ x : X, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y : X, distance d.toPseudoMetricSpace y x < δ →
        distance e.toPseudoMetricSpace (f y) (f x) < ε

def metric_closure_iff_balls : Prop :=
  ∀ {X : Type u} (d : MetricSpace X) (A : Set X) (x : X),
    x ∈ @closure X (metricTopology d.toPseudoMetricSpace) A ↔
      ∀ r : ℝ, 0 < r → (ball d.toPseudoMetricSpace x r ∩ A).Nonempty

/-- Ordinary sequence convergence is topological convergence. The scalar
limit on the right uses the usual real topology. -/
def metric_sequence_iff_distance_zero : Prop :=
  ∀ {X : Type u} (d : MetricSpace X) (s : ℕ → X) (x : X),
    Tendsto s atTop (@nhds X (metricTopology d.toPseudoMetricSpace) x) ↔
      Tendsto (fun n => distance d.toPseudoMetricSpace (s n) x) atTop (𝓝 (0 : ℝ))

end Specs.D10Topology.Ch09.MetricTopology
